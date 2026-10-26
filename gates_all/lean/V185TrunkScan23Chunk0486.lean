import V185TrunkScan23Chunk0485

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2875039 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2875039 : Nat := 118140960795 + 2875039 * 2 ^ 59
def prefixEnd_2875039 : Nat := 4983230072969 + 3 ^ 40 * 2875039 * 2
def baseEnd_2875039 : Nat := 1476276907421882130390443

theorem tailTrace_2875039 : CollatzResearch.WordTrace tailWord_2875039 prefixEnd_2875039 1476276907421882130390443 := by
  unfold tailWord_2875039
  simp only [CollatzResearch.WordTrace]
  refine ⟨104861287031232195414404171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69907524687488130276269447 104861287031232195414404171)
  ·
    refine ⟨157291930546848293121606257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104861287031232195414404171 157291930546848293121606257)
    ·
      refine ⟨117968947910136219841204693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157291930546848293121606257 117968947910136219841204693)
      ·
        refine ⟨2764897216643817652528235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 117968947910136219841204693 2764897216643817652528235)
        ·
          refine ⟨4147345824965726478792353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764897216643817652528235 4147345824965726478792353)
          ·
            refine ⟨3110509368724294859094265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4147345824965726478792353 3110509368724294859094265)
            ·
              refine ⟨2332882026543221144320699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3110509368724294859094265 2332882026543221144320699)
              ·
                refine ⟨3499323039814831716481049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332882026543221144320699 3499323039814831716481049)
                ·
                  refine ⟨2624492279861123787360787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499323039814831716481049 2624492279861123787360787)
                  ·
                    refine ⟨3936738419791685681041181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624492279861123787360787 3936738419791685681041181)
                    ·
                      refine ⟨1476276907421882130390443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3936738419791685681041181 1476276907421882130390443)
                      ·
                        rfl

theorem cell23_2875039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2875039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875039 prefixEnd_2875039 := by exact prefixLift 2875039
  have htrace : WordTrace (prefixWord ++ tailWord_2875039) baseStart_2875039 baseEnd_2875039 := by
    simpa [prefixWord, tailWord_2875039, baseEnd_2875039] using wordTrace_append hprefix tailTrace_2875039
  have hstable : (prefixWord ++ tailWord_2875039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875039).length < 2 ^ (prefixWord ++ tailWord_2875039).sum := by decide
  have hdescent : baseEnd_2875039 < baseStart_2875039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875062 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2875062 : Nat := 118140960795 + 2875062 * 2 ^ 59
def prefixEnd_2875062 : Nat := 4983230072969 + 3 ^ 40 * 2875062 * 2
def baseEnd_2875062 : Nat := 1476288717476935540402837

theorem tailTrace_2875062 : CollatzResearch.WordTrace tailWord_2875062 prefixEnd_2875062 1476288717476935540402837 := by
  unfold tailWord_2875062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553882869384304396405715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69908083940099246894994293 6553882869384304396405715)
  ·
    refine ⟨9830824304076456594608573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553882869384304396405715 9830824304076456594608573)
    ·
      refine ⟨3686559114028671222978215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9830824304076456594608573 3686559114028671222978215)
      ·
        refine ⟨5529838671043006834467323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686559114028671222978215 5529838671043006834467323)
        ·
          refine ⟨8294758006564510251700985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529838671043006834467323 8294758006564510251700985)
          ·
            refine ⟨6221068504923382688775739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8294758006564510251700985 6221068504923382688775739)
            ·
              refine ⟨9331602757385074033163609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221068504923382688775739 9331602757385074033163609)
              ·
                refine ⟨6998702068038805524872707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331602757385074033163609 6998702068038805524872707)
                ·
                  refine ⟨10498053102058208287309061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6998702068038805524872707 10498053102058208287309061)
                  ·
                    refine ⟨1968384956635914053870449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10498053102058208287309061 1968384956635914053870449)
                    ·
                      refine ⟨1476288717476935540402837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968384956635914053870449 1476288717476935540402837)
                      ·
                        rfl

theorem cell23_2875062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2875062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875062 prefixEnd_2875062 := by exact prefixLift 2875062
  have htrace : WordTrace (prefixWord ++ tailWord_2875062) baseStart_2875062 baseEnd_2875062 := by
    simpa [prefixWord, tailWord_2875062, baseEnd_2875062] using wordTrace_append hprefix tailTrace_2875062
  have hstable : (prefixWord ++ tailWord_2875062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875062).length < 2 ^ (prefixWord ++ tailWord_2875062).sum := by decide
  have hdescent : baseEnd_2875062 < baseStart_2875062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875064 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_2875064 : Nat := 118140960795 + 2875064 * 2 ^ 59
def prefixEnd_2875064 : Nat := 4983230072969 + 3 ^ 40 * 2875064 * 2
def baseEnd_2875064 : Nat := 492096581479414844192609

theorem tailTrace_2875064 : CollatzResearch.WordTrace tailWord_2875064 prefixEnd_2875064 492096581479414844192609 := by
  unfold tailWord_2875064
  simp only [CollatzResearch.WordTrace]
  refine ⟨52431099428070812342032123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69908132570761083122709497 52431099428070812342032123)
  ·
    refine ⟨78646649142106218513048185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52431099428070812342032123 78646649142106218513048185)
    ·
      refine ⟨58984986856579663884786139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78646649142106218513048185 58984986856579663884786139)
      ·
        refine ⟨88477480284869495827179209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58984986856579663884786139 88477480284869495827179209)
        ·
          refine ⟨66358110213652121870384407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88477480284869495827179209 66358110213652121870384407)
          ·
            refine ⟨99537165320478182805576611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66358110213652121870384407 99537165320478182805576611)
            ·
              refine ⟨149305747980717274208364917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99537165320478182805576611 149305747980717274208364917)
              ·
                refine ⟨13997413873192244457034211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149305747980717274208364917 13997413873192244457034211)
                ·
                  refine ⟨20996120809788366685551317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13997413873192244457034211 20996120809788366685551317)
                  ·
                    refine ⟨492096581479414844192609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20996120809788366685551317 492096581479414844192609)
                    ·
                      rfl

theorem cell23_2875064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_2875064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875064 prefixEnd_2875064 := by exact prefixLift 2875064
  have htrace : WordTrace (prefixWord ++ tailWord_2875064) baseStart_2875064 baseEnd_2875064 := by
    simpa [prefixWord, tailWord_2875064, baseEnd_2875064] using wordTrace_append hprefix tailTrace_2875064
  have hstable : (prefixWord ++ tailWord_2875064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875064).length < 2 ^ (prefixWord ++ tailWord_2875064).sum := by decide
  have hdescent : baseEnd_2875064 < baseStart_2875064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875118 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_2875118 : Nat := 118140960795 + 2875118 * 2 ^ 59
def prefixEnd_2875118 : Nat := 4983230072969 + 3 ^ 40 * 2875118 * 2
def baseEnd_2875118 : Nat := 1476317472393587321302579

theorem tailTrace_2875118 : CollatzResearch.WordTrace tailWord_2875118 prefixEnd_2875118 1476317472393587321302579 := by
  unfold tailWord_2875118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13108021049743248988316251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69909445598630661271020005 13108021049743248988316251)
  ·
    refine ⟨19662031574614873482474377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13108021049743248988316251 19662031574614873482474377)
    ·
      refine ⟨14746523680961155111855783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19662031574614873482474377 14746523680961155111855783)
      ·
        refine ⟨22119785521441732667783675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14746523680961155111855783 22119785521441732667783675)
        ·
          refine ⟨33179678282162599001675513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22119785521441732667783675 33179678282162599001675513)
          ·
            refine ⟨24884758711621949251256635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33179678282162599001675513 24884758711621949251256635)
            ·
              refine ⟨37327138067432923876884953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24884758711621949251256635 37327138067432923876884953)
              ·
                refine ⟨27995353550574692907663715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37327138067432923876884953 27995353550574692907663715)
                ·
                  refine ⟨41993030325862039361495573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27995353550574692907663715 41993030325862039361495573)
                  ·
                    refine ⟨1968423296524783095070105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41993030325862039361495573 1968423296524783095070105)
                    ·
                      refine ⟨1476317472393587321302579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968423296524783095070105 1476317472393587321302579)
                      ·
                        rfl

theorem cell23_2875118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_2875118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875118 prefixEnd_2875118 := by exact prefixLift 2875118
  have htrace : WordTrace (prefixWord ++ tailWord_2875118) baseStart_2875118 baseEnd_2875118 := by
    simpa [prefixWord, tailWord_2875118, baseEnd_2875118] using wordTrace_append hprefix tailTrace_2875118
  have hstable : (prefixWord ++ tailWord_2875118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875118).length < 2 ^ (prefixWord ++ tailWord_2875118).sum := by decide
  have hdescent : baseEnd_2875118 < baseStart_2875118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875171 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 3, 5]
def baseStart_2875171 : Nat := 118140960795 + 2875171 * 2 ^ 59
def prefixEnd_2875171 : Nat := 4983230072969 + 3 ^ 40 * 2875171 * 2
def baseEnd_2875171 : Nat := 492114895622758537979945

theorem tailTrace_2875171 : CollatzResearch.WordTrace tailWord_2875171 prefixEnd_2875171 492114895622758537979945 := by
  unfold tailWord_2875171
  simp only [CollatzResearch.WordTrace]
  refine ⟨104866101466753981958209367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69910734311169321305472911 104866101466753981958209367)
  ·
    refine ⟨157299152200130972937314051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104866101466753981958209367 157299152200130972937314051)
    ·
      refine ⟨235948728300196459405971077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157299152200130972937314051 235948728300196459405971077)
      ·
        refine ⟨44240386556286836138619577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235948728300196459405971077 44240386556286836138619577)
        ·
          refine ⟨33180289917215127103964683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44240386556286836138619577 33180289917215127103964683)
          ·
            refine ⟨49770434875822690655947025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33180289917215127103964683 49770434875822690655947025)
            ·
              refine ⟨37327826156867017991960269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49770434875822690655947025 37327826156867017991960269)
              ·
                refine ⟨13997934808825131746985101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37327826156867017991960269 13997934808825131746985101)
                ·
                  refine ⟨5249225553309424405119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13997934808825131746985101 5249225553309424405119413)
                  ·
                    refine ⟨492114895622758537979945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5249225553309424405119413 492114895622758537979945)
                    ·
                      rfl

theorem cell23_2875171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 5].length) (baseStart_2875171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875171 prefixEnd_2875171 := by exact prefixLift 2875171
  have htrace : WordTrace (prefixWord ++ tailWord_2875171) baseStart_2875171 baseEnd_2875171 := by
    simpa [prefixWord, tailWord_2875171, baseEnd_2875171] using wordTrace_append hprefix tailTrace_2875171
  have hstable : (prefixWord ++ tailWord_2875171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875171).length < 2 ^ (prefixWord ++ tailWord_2875171).sum := by decide
  have hdescent : baseEnd_2875171 < baseStart_2875171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875225 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 5, 2, 2]
def baseStart_2875225 : Nat := 118140960795 + 2875225 * 2 ^ 59
def prefixEnd_2875225 : Nat := 4983230072969 + 3 ^ 40 * 2875225 * 2
def baseEnd_2875225 : Nat := 1476372414823618402664587

theorem tailTrace_2875225 : CollatzResearch.WordTrace tailWord_2875225 prefixEnd_2875225 1476372414823618402664587 := by
  unfold tailWord_2875225
  simp only [CollatzResearch.WordTrace]
  refine ⟨104868071008558349180675129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69912047339038899453783419 104868071008558349180675129)
  ·
    refine ⟨78651053256418761885506347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104868071008558349180675129 78651053256418761885506347)
    ·
      refine ⟨117976579884628142828259521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78651053256418761885506347 117976579884628142828259521)
      ·
        refine ⟨88482434913471107121194641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117976579884628142828259521 88482434913471107121194641)
        ·
          refine ⟨66361826185103330340895981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88482434913471107121194641 66361826185103330340895981)
          ·
            refine ⟨24885684819413748877835993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66361826185103330340895981 24885684819413748877835993)
            ·
              refine ⟨18664263614560311658376995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24885684819413748877835993 18664263614560311658376995)
              ·
                refine ⟨27996395421840467487565493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18664263614560311658376995 27996395421840467487565493)
                ·
                  refine ⟨2624662070797543826959265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27996395421840467487565493 2624662070797543826959265)
                  ·
                    refine ⟨1968496553098157870219449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2624662070797543826959265 1968496553098157870219449)
                    ·
                      refine ⟨1476372414823618402664587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968496553098157870219449 1476372414823618402664587)
                      ·
                        rfl

theorem cell23_2875225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_2875225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875225 prefixEnd_2875225 := by exact prefixLift 2875225
  have htrace : WordTrace (prefixWord ++ tailWord_2875225) baseStart_2875225 baseEnd_2875225 := by
    simpa [prefixWord, tailWord_2875225, baseEnd_2875225] using wordTrace_append hprefix tailTrace_2875225
  have hstable : (prefixWord ++ tailWord_2875225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875225).length < 2 ^ (prefixWord ++ tailWord_2875225).sum := by decide
  have hdescent : baseEnd_2875225 < baseStart_2875225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875231 : List Nat := [1, 1, 2, 3, 1, 4, 2, 9]
def baseStart_2875231 : Nat := 118140960795 + 2875231 * 2 ^ 59
def prefixEnd_2875231 : Nat := 4983230072969 + 3 ^ 40 * 2875231 * 2
def baseEnd_2875231 : Nat := 54680573915094273303317

theorem tailTrace_2875231 : CollatzResearch.WordTrace tailWord_2875231 prefixEnd_2875231 54680573915094273303317 := by
  unfold tailWord_2875231
  simp only [CollatzResearch.WordTrace]
  refine ⟨104868289846536612205393547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69912193231024408136929031 104868289846536612205393547)
  ·
    refine ⟨157302434769804918308090321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104868289846536612205393547 157302434769804918308090321)
    ·
      refine ⟨117976826077353688731067741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157302434769804918308090321 117976826077353688731067741)
      ·
        refine ⟨44241309779007633274150403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117976826077353688731067741 44241309779007633274150403)
        ·
          refine ⟨66361964668511449911225605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44241309779007633274150403 66361964668511449911225605)
          ·
            refine ⟨12442868375345896858354801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66361964668511449911225605 12442868375345896858354801)
            ·
              refine ⟨9332151281509422643766101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12442868375345896858354801 9332151281509422643766101)
              ·
                refine ⟨54680573915094273303317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9332151281509422643766101 54680573915094273303317)
                ·
                  rfl

theorem cell23_2875231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 9].length) (baseStart_2875231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875231 prefixEnd_2875231 := by exact prefixLift 2875231
  have htrace : WordTrace (prefixWord ++ tailWord_2875231) baseStart_2875231 baseEnd_2875231 := by
    simpa [prefixWord, tailWord_2875231, baseEnd_2875231] using wordTrace_append hprefix tailTrace_2875231
  have hstable : (prefixWord ++ tailWord_2875231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875231).length < 2 ^ (prefixWord ++ tailWord_2875231).sum := by decide
  have hdescent : baseEnd_2875231 < baseStart_2875231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875245 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2875245 : Nat := 118140960795 + 2875245 * 2 ^ 59
def prefixEnd_2875245 : Nat := 4983230072969 + 3 ^ 40 * 2875245 * 2
def baseEnd_2875245 : Nat := 1476382684436708324414495

theorem tailTrace_2875245 : CollatzResearch.WordTrace tailWord_2875245 prefixEnd_2875245 1476382684436708324414495 := by
  unfold tailWord_2875245
  simp only [CollatzResearch.WordTrace]
  refine ⟨104868800468485892596403189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69912533645657261730935459 104868800468485892596403189)
  ·
    refine ⟨9831450043920552430912799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104868800468485892596403189 9831450043920552430912799)
    ·
      refine ⟨14747175065880828646369199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9831450043920552430912799 14747175065880828646369199)
      ·
        refine ⟨22120762598821242969553799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14747175065880828646369199 22120762598821242969553799)
        ·
          refine ⟨33181143898231864454330699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22120762598821242969553799 33181143898231864454330699)
          ·
            refine ⟨49771715847347796681496049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33181143898231864454330699 49771715847347796681496049)
            ·
              refine ⟨37328786885510847511122037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49771715847347796681496049 37328786885510847511122037)
              ·
                refine ⟨3499573770516641954167691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37328786885510847511122037 3499573770516641954167691)
                ·
                  refine ⟨5249360655774962931251537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499573770516641954167691 5249360655774962931251537)
                  ·
                    refine ⟨3937020491831222198438653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5249360655774962931251537 3937020491831222198438653)
                    ·
                      refine ⟨1476382684436708324414495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937020491831222198438653 1476382684436708324414495)
                      ·
                        rfl

theorem cell23_2875245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2875245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875245 prefixEnd_2875245 := by exact prefixLift 2875245
  have htrace : WordTrace (prefixWord ++ tailWord_2875245) baseStart_2875245 baseEnd_2875245 := by
    simpa [prefixWord, tailWord_2875245, baseEnd_2875245] using wordTrace_append hprefix tailTrace_2875245
  have hstable : (prefixWord ++ tailWord_2875245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875245).length < 2 ^ (prefixWord ++ tailWord_2875245).sum := by decide
  have hdescent : baseEnd_2875245 < baseStart_2875245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875262 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2875262 : Nat := 118140960795 + 2875262 * 2 ^ 59
def prefixEnd_2875262 : Nat := 4983230072969 + 3 ^ 40 * 2875262 * 2
def baseEnd_2875262 : Nat := 1476391413607834757901917

theorem tailTrace_2875262 : CollatzResearch.WordTrace tailWord_2875262 prefixEnd_2875262 1476391413607834757901917 := by
  unfold tailWord_2875262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13108677563678038062471505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69912947006282869666514693 13108677563678038062471505)
  ·
    refine ⟨9831508172758528546853629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13108677563678038062471505 9831508172758528546853629)
    ·
      refine ⟨3686815564784448205070111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9831508172758528546853629 3686815564784448205070111)
      ·
        refine ⟨5530223347176672307605167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686815564784448205070111 5530223347176672307605167)
        ·
          refine ⟨8295335020765008461407751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530223347176672307605167 8295335020765008461407751)
          ·
            refine ⟨12443002531147512692111627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8295335020765008461407751 12443002531147512692111627)
            ·
              refine ⟨18664503796721269038167441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12443002531147512692111627 18664503796721269038167441)
              ·
                refine ⟨13998377847540951778625581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18664503796721269038167441 13998377847540951778625581)
                ·
                  refine ⟨5249391692827856916984593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13998377847540951778625581 5249391692827856916984593)
                  ·
                    refine ⟨3937043769620892687738445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5249391692827856916984593 3937043769620892687738445)
                    ·
                      refine ⟨1476391413607834757901917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937043769620892687738445 1476391413607834757901917)
                      ·
                        rfl

theorem cell23_2875262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2875262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875262 prefixEnd_2875262 := by exact prefixLift 2875262
  have htrace : WordTrace (prefixWord ++ tailWord_2875262) baseStart_2875262 baseEnd_2875262 := by
    simpa [prefixWord, tailWord_2875262, baseEnd_2875262] using wordTrace_append hprefix tailTrace_2875262
  have hstable : (prefixWord ++ tailWord_2875262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875262).length < 2 ^ (prefixWord ++ tailWord_2875262).sum := by decide
  have hdescent : baseEnd_2875262 < baseStart_2875262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875285 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_2875285 : Nat := 118140960795 + 2875285 * 2 ^ 59
def prefixEnd_2875285 : Nat := 4983230072969 + 3 ^ 40 * 2875285 * 2
def baseEnd_2875285 : Nat := 1476403223662888167914311

theorem tailTrace_2875285 : CollatzResearch.WordTrace tailWord_2875285 prefixEnd_2875285 1476403223662888167914311 := by
  unfold tailWord_2875285
  simp only [CollatzResearch.WordTrace]
  refine ⟨104870259388340979427859309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69913506258893986285239539 104870259388340979427859309)
  ·
    refine ⟨39326347270627867285447241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104870259388340979427859309 39326347270627867285447241)
    ·
      refine ⟨29494760452970900464085431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39326347270627867285447241 29494760452970900464085431)
      ·
        refine ⟨44242140679456350696128147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29494760452970900464085431 44242140679456350696128147)
        ·
          refine ⟨66363211019184526044192221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44242140679456350696128147 66363211019184526044192221)
          ·
            refine ⟨24886204132194197266572083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66363211019184526044192221 24886204132194197266572083)
            ·
              refine ⟨37329306198291295899858125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24886204132194197266572083 37329306198291295899858125)
              ·
                refine ⟨13998489824359235962446797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37329306198291295899858125 13998489824359235962446797)
                ·
                  refine ⟨5249433684134713485917549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13998489824359235962446797 5249433684134713485917549)
                  ·
                    refine ⟨1968537631550517557219081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5249433684134713485917549 1968537631550517557219081)
                    ·
                      refine ⟨1476403223662888167914311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968537631550517557219081 1476403223662888167914311)
                      ·
                        rfl

theorem cell23_2875285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_2875285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875285 prefixEnd_2875285 := by exact prefixLift 2875285
  have htrace : WordTrace (prefixWord ++ tailWord_2875285) baseStart_2875285 baseEnd_2875285 := by
    simpa [prefixWord, tailWord_2875285, baseEnd_2875285] using wordTrace_append hprefix tailTrace_2875285
  have hstable : (prefixWord ++ tailWord_2875285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875285).length < 2 ^ (prefixWord ++ tailWord_2875285).sum := by decide
  have hdescent : baseEnd_2875285 < baseStart_2875285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875328 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_2875328 : Nat := 118140960795 + 2875328 * 2 ^ 59
def prefixEnd_2875328 : Nat := 4983230072969 + 3 ^ 40 * 2875328 * 2
def baseEnd_2875328 : Nat := 1476425303331031499676613

theorem tailTrace_2875328 : CollatzResearch.WordTrace tailWord_2875328 prefixEnd_2875328 1476425303331031499676613 := by
  unfold tailWord_2875328
  simp only [CollatzResearch.WordTrace]
  refine ⟨52435913863592598885837319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69914551818123465181116425 52435913863592598885837319)
  ·
    refine ⟨78653870795388898328755979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52435913863592598885837319 78653870795388898328755979)
    ·
      refine ⟨117980806193083347493133969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78653870795388898328755979 117980806193083347493133969)
      ·
        refine ⟨88485604644812510619850477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117980806193083347493133969 88485604644812510619850477)
        ·
          refine ⟨33182101741804691482443929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88485604644812510619850477 33182101741804691482443929)
          ·
            refine ⟨24886576306353518611832947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33182101741804691482443929 24886576306353518611832947)
            ·
              refine ⟨37329864459530277917749421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24886576306353518611832947 37329864459530277917749421)
              ·
                refine ⟨13998699172323854219156033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37329864459530277917749421 13998699172323854219156033)
                ·
                  refine ⟨10499024379242890664367025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13998699172323854219156033 10499024379242890664367025)
                  ·
                    refine ⟨7874268284432167998275269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10499024379242890664367025 7874268284432167998275269)
                    ·
                      refine ⟨1476425303331031499676613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7874268284432167998275269 1476425303331031499676613)
                      ·
                        rfl

theorem cell23_2875328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_2875328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875328 prefixEnd_2875328 := by exact prefixLift 2875328
  have htrace : WordTrace (prefixWord ++ tailWord_2875328) baseStart_2875328 baseEnd_2875328 := by
    simpa [prefixWord, tailWord_2875328, baseEnd_2875328] using wordTrace_append hprefix tailTrace_2875328
  have hstable : (prefixWord ++ tailWord_2875328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875328).length < 2 ^ (prefixWord ++ tailWord_2875328).sum := by decide
  have hdescent : baseEnd_2875328 < baseStart_2875328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875338 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_2875338 : Nat := 118140960795 + 2875338 * 2 ^ 59
def prefixEnd_2875338 : Nat := 4983230072969 + 3 ^ 40 * 2875338 * 2
def baseEnd_2875338 : Nat := 164047826459730717839063

theorem tailTrace_2875338 : CollatzResearch.WordTrace tailWord_2875338 prefixEnd_2875338 164047826459730717839063 := by
  unfold tailWord_2875338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218048114287242369884667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69914794971432646319692445 26218048114287242369884667)
  ·
    refine ⟨39327072171430863554827001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26218048114287242369884667 39327072171430863554827001)
    ·
      refine ⟨29495304128573147666120251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39327072171430863554827001 29495304128573147666120251)
      ·
        refine ⟨44242956192859721499180377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29495304128573147666120251 44242956192859721499180377)
        ·
          refine ⟨33182217144644791124385283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44242956192859721499180377 33182217144644791124385283)
          ·
            refine ⟨49773325716967186686577925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33182217144644791124385283 49773325716967186686577925)
            ·
              refine ⟨9332498571931347503733361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49773325716967186686577925 9332498571931347503733361)
              ·
                refine ⟨6999373928948510627800021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9332498571931347503733361 6999373928948510627800021)
                ·
                  refine ⟨164047826459730717839063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6999373928948510627800021 164047826459730717839063)
                  ·
                    rfl

theorem cell23_2875338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_2875338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875338 prefixEnd_2875338 := by exact prefixLift 2875338
  have htrace : WordTrace (prefixWord ++ tailWord_2875338) baseStart_2875338 baseEnd_2875338 := by
    simpa [prefixWord, tailWord_2875338, baseEnd_2875338] using wordTrace_append hprefix tailTrace_2875338
  have hstable : (prefixWord ++ tailWord_2875338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875338).length < 2 ^ (prefixWord ++ tailWord_2875338).sum := by decide
  have hdescent : baseEnd_2875338 < baseStart_2875338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875375 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 5, 2]
def baseStart_2875375 : Nat := 118140960795 + 2875375 * 2 ^ 59
def prefixEnd_2875375 : Nat := 4983230072969 + 3 ^ 40 * 2875375 * 2
def baseEnd_2875375 : Nat := 1476449436921792815788897

theorem tailTrace_2875375 : CollatzResearch.WordTrace tailWord_2875375 prefixEnd_2875375 1476449436921792815788897 := by
  unfold tailWord_2875375
  simp only [CollatzResearch.WordTrace]
  refine ⟨104873541958014924798635579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69915694638676616532423719 104873541958014924798635579)
  ·
    refine ⟨157310312937022387197953369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104873541958014924798635579 157310312937022387197953369)
    ·
      refine ⟨117982734702766790398465027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157310312937022387197953369 117982734702766790398465027)
      ·
        refine ⟨176974102054150185597697541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117982734702766790398465027 176974102054150185597697541)
        ·
          refine ⟨33182644135153159799568289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176974102054150185597697541 33182644135153159799568289)
          ·
            refine ⟨24886983101364869849676217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33182644135153159799568289 24886983101364869849676217)
            ·
              refine ⟨18665237326023652387257163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24886983101364869849676217 18665237326023652387257163)
              ·
                refine ⟨27997855989035478580885745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18665237326023652387257163 27997855989035478580885745)
                ·
                  refine ⟨20998391991776608935664309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27997855989035478580885745 20998391991776608935664309)
                  ·
                    refine ⟨1968599249229057087718529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20998391991776608935664309 1968599249229057087718529)
                    ·
                      refine ⟨1476449436921792815788897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968599249229057087718529 1476449436921792815788897)
                      ·
                        rfl

theorem cell23_2875375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5, 2].length) (baseStart_2875375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875375 prefixEnd_2875375 := by exact prefixLift 2875375
  have htrace : WordTrace (prefixWord ++ tailWord_2875375) baseStart_2875375 baseEnd_2875375 := by
    simpa [prefixWord, tailWord_2875375, baseEnd_2875375] using wordTrace_append hprefix tailTrace_2875375
  have hstable : (prefixWord ++ tailWord_2875375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875375).length < 2 ^ (prefixWord ++ tailWord_2875375).sum := by decide
  have hdescent : baseEnd_2875375 < baseStart_2875375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875402 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_2875402 : Nat := 118140960795 + 2875402 * 2 ^ 59
def prefixEnd_2875402 : Nat := 4983230072969 + 3 ^ 40 * 2875402 * 2
def baseEnd_2875402 : Nat := 492154433633154736717091

theorem tailTrace_2875402 : CollatzResearch.WordTrace tailWord_2875402 prefixEnd_2875402 492154433633154736717091 := by
  unfold tailWord_2875402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218631682229277102467115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69916351152611405606578973 26218631682229277102467115)
  ·
    refine ⟨39327947523343915653700673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26218631682229277102467115 39327947523343915653700673)
    ·
      refine ⟨29495960642507936740275505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39327947523343915653700673 29495960642507936740275505)
      ·
        refine ⟨22121970481880952555206629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29495960642507936740275505 22121970481880952555206629)
        ·
          refine ⟨4147869465352678604101243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22121970481880952555206629 4147869465352678604101243)
          ·
            refine ⟨6221804198029017906151865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147869465352678604101243 6221804198029017906151865)
            ·
              refine ⟨4666353148521763429613899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6221804198029017906151865 4666353148521763429613899)
              ·
                refine ⟨6999529722782645144420849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666353148521763429613899 6999529722782645144420849)
                ·
                  refine ⟨5249647292086983858315637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6999529722782645144420849 5249647292086983858315637)
                  ·
                    refine ⟨492154433633154736717091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5249647292086983858315637 492154433633154736717091)
                    ·
                      rfl

theorem cell23_2875402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_2875402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875402 prefixEnd_2875402 := by exact prefixLift 2875402
  have htrace : WordTrace (prefixWord ++ tailWord_2875402) baseStart_2875402 baseEnd_2875402 := by
    simpa [prefixWord, tailWord_2875402, baseEnd_2875402] using wordTrace_append hprefix tailTrace_2875402
  have hstable : (prefixWord ++ tailWord_2875402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875402).length < 2 ^ (prefixWord ++ tailWord_2875402).sum := by decide
  have hdescent : baseEnd_2875402 < baseStart_2875402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875445 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 6]
def baseStart_2875445 : Nat := 118140960795 + 2875445 * 2 ^ 59
def prefixEnd_2875445 : Nat := 4983230072969 + 3 ^ 40 * 2875445 * 2
def baseEnd_2875445 : Nat := 164053931174178615768175

theorem tailTrace_2875445 : CollatzResearch.WordTrace tailWord_2875445 prefixEnd_2875445 164053931174178615768175 := by
  unfold tailWord_2875445
  simp only [CollatzResearch.WordTrace]
  refine ⟨104876095067761326753683789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69917396711840884502455859 104876095067761326753683789)
  ·
    refine ⟨39328535650410497532631421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104876095067761326753683789 39328535650410497532631421)
    ·
      refine ⟨14748200868903936574736783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39328535650410497532631421 14748200868903936574736783)
      ·
        refine ⟨22122301303355904862105175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14748200868903936574736783 22122301303355904862105175)
        ·
          refine ⟨33183451955033857293157763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22122301303355904862105175 33183451955033857293157763)
          ·
            refine ⟨49775177932550785939736645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33183451955033857293157763 49775177932550785939736645)
            ·
              refine ⟨9332845862353272363700621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49775177932550785939736645 9332845862353272363700621)
              ·
                refine ⟨3499817198382477136387733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9332845862353272363700621 3499817198382477136387733)
                ·
                  refine ⟨164053931174178615768175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3499817198382477136387733 164053931174178615768175)
                  ·
                    rfl

theorem cell23_2875445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_2875445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875445 prefixEnd_2875445 := by exact prefixLift 2875445
  have htrace : WordTrace (prefixWord ++ tailWord_2875445) baseStart_2875445 baseEnd_2875445 := by
    simpa [prefixWord, tailWord_2875445, baseEnd_2875445] using wordTrace_append hprefix tailTrace_2875445
  have hstable : (prefixWord ++ tailWord_2875445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875445).length < 2 ^ (prefixWord ++ tailWord_2875445).sum := by decide
  have hdescent : baseEnd_2875445 < baseStart_2875445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875462 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2875462 : Nat := 118140960795 + 2875462 * 2 ^ 59
def prefixEnd_2875462 : Nat := 4983230072969 + 3 ^ 40 * 2875462 * 2
def baseEnd_2875462 : Nat := 164054901082081552822333

theorem tailTrace_2875462 : CollatzResearch.WordTrace tailWord_2875462 prefixEnd_2875462 164054901082081552822333 := by
  unfold tailWord_2875462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277397347146866833032895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69917810072466492438035093 3277397347146866833032895)
  ·
    refine ⟨4916096020720300249549343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277397347146866833032895 4916096020720300249549343)
    ·
      refine ⟨7374144031080450374324015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916096020720300249549343 7374144031080450374324015)
      ·
        refine ⟨11061216046620675561486023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374144031080450374324015 11061216046620675561486023)
        ·
          refine ⟨16591824069931013342229035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11061216046620675561486023 16591824069931013342229035)
          ·
            refine ⟨24887736104896520013343553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16591824069931013342229035 24887736104896520013343553)
            ·
              refine ⟨18665802078672390010007665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24887736104896520013343553 18665802078672390010007665)
              ·
                refine ⟨13999351559004292507505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18665802078672390010007665 13999351559004292507505749)
                ·
                  refine ⟨164054901082081552822333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13999351559004292507505749 164054901082081552822333)
                  ·
                    rfl

theorem cell23_2875462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2875462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875462 prefixEnd_2875462 := by exact prefixLift 2875462
  have htrace : WordTrace (prefixWord ++ tailWord_2875462) baseStart_2875462 baseEnd_2875462 := by
    simpa [prefixWord, tailWord_2875462, baseEnd_2875462] using wordTrace_append hprefix tailTrace_2875462
  have hstable : (prefixWord ++ tailWord_2875462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875462).length < 2 ^ (prefixWord ++ tailWord_2875462).sum := by decide
  have hdescent : baseEnd_2875462 < baseStart_2875462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875482 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_2875482 : Nat := 118140960795 + 2875482 * 2 ^ 59
def prefixEnd_2875482 : Nat := 4983230072969 + 3 ^ 40 * 2875482 * 2
def baseEnd_2875482 : Nat := 1476504379351823897150905

theorem tailTrace_2875482 : CollatzResearch.WordTrace tailWord_2875482 prefixEnd_2875482 1476504379351823897150905 := by
  unfold tailWord_2875482
  simp only [CollatzResearch.WordTrace]
  refine ⟨26219361142156820518195175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69918296379084854715187133 26219361142156820518195175)
  ·
    refine ⟨39329041713235230777292763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26219361142156820518195175 39329041713235230777292763)
    ·
      refine ⟨58993562569852846165939145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39329041713235230777292763 58993562569852846165939145)
      ·
        refine ⟨44245171927389634624454359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58993562569852846165939145 44245171927389634624454359)
        ·
          refine ⟨66367757891084451936681539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44245171927389634624454359 66367757891084451936681539)
          ·
            refine ⟨99551636836626677905022309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66367757891084451936681539 99551636836626677905022309)
            ·
              refine ⟨18665931906867502107191683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99551636836626677905022309 18665931906867502107191683)
              ·
                refine ⟨27998897860301253160787525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18665931906867502107191683 27998897860301253160787525)
                ·
                  refine ⟨5249793348806484967647661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27998897860301253160787525 5249793348806484967647661)
                  ·
                    refine ⟨1968672505802431862867873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5249793348806484967647661 1968672505802431862867873)
                    ·
                      refine ⟨1476504379351823897150905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968672505802431862867873 1476504379351823897150905)
                      ·
                        rfl

theorem cell23_2875482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_2875482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875482 prefixEnd_2875482 := by exact prefixLift 2875482
  have htrace : WordTrace (prefixWord ++ tailWord_2875482) baseStart_2875482 baseEnd_2875482 := by
    simpa [prefixWord, tailWord_2875482, baseEnd_2875482] using wordTrace_append hprefix tailTrace_2875482
  have hstable : (prefixWord ++ tailWord_2875482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875482).length < 2 ^ (prefixWord ++ tailWord_2875482).sum := by decide
  have hdescent : baseEnd_2875482 < baseStart_2875482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875540 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2875540 : Nat := 118140960795 + 2875540 * 2 ^ 59
def prefixEnd_2875540 : Nat := 4983230072969 + 3 ^ 40 * 2875540 * 2
def baseEnd_2875540 : Nat := 1476534161229784670225639

theorem tailTrace_2875540 : CollatzResearch.WordTrace tailWord_2875540 prefixEnd_2875540 1476534161229784670225639 := by
  unfold tailWord_2875540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52439780001208578989196037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69919706668278105318928049 52439780001208578989196037)
  ·
    refine ⟨9832458750226608560474257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52439780001208578989196037 9832458750226608560474257)
    ·
      refine ⟨7374344062669956420355693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9832458750226608560474257 7374344062669956420355693)
      ·
        refine ⟨2765379023501233657633385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7374344062669956420355693 2765379023501233657633385)
        ·
          refine ⟨2074034267625925243225039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765379023501233657633385 2074034267625925243225039)
          ·
            refine ⟨3111051401438887864837559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074034267625925243225039 3111051401438887864837559)
            ·
              refine ⟨4666577102158331797256339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111051401438887864837559 4666577102158331797256339)
              ·
                refine ⟨6999865653237497695884509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4666577102158331797256339 6999865653237497695884509)
                ·
                  refine ⟨2624949619964061635956691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6999865653237497695884509 2624949619964061635956691)
                  ·
                    refine ⟨3937424429946092453935037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2624949619964061635956691 3937424429946092453935037)
                    ·
                      refine ⟨1476534161229784670225639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937424429946092453935037 1476534161229784670225639)
                      ·
                        rfl

theorem cell23_2875540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2875540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875540 prefixEnd_2875540 := by exact prefixLift 2875540
  have htrace : WordTrace (prefixWord ++ tailWord_2875540) baseStart_2875540 baseEnd_2875540 := by
    simpa [prefixWord, tailWord_2875540, baseEnd_2875540] using wordTrace_append hprefix tailTrace_2875540
  have hstable : (prefixWord ++ tailWord_2875540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875540).length < 2 ^ (prefixWord ++ tailWord_2875540).sum := by decide
  have hdescent : baseEnd_2875540 < baseStart_2875540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875589 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_2875589 : Nat := 118140960795 + 2875589 * 2 ^ 59
def prefixEnd_2875589 : Nat := 4983230072969 + 3 ^ 40 * 2875589 * 2
def baseEnd_2875589 : Nat := 1476559321781854978512913

theorem tailTrace_2875589 : CollatzResearch.WordTrace tailWord_2875589 prefixEnd_2875589 1476559321781854978512913 := by
  unfold tailWord_2875589
  simp only [CollatzResearch.WordTrace]
  refine ⟨104881347179239639346925821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69920898119493092897950547 104881347179239639346925821)
  ·
    refine ⟨39330505192214864755097183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104881347179239639346925821 39330505192214864755097183)
    ·
      refine ⟨58995757788322297132645775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39330505192214864755097183 58995757788322297132645775)
      ·
        refine ⟨88493636682483445698968663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58995757788322297132645775 88493636682483445698968663)
        ·
          refine ⟨132740455023725168548452995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88493636682483445698968663 132740455023725168548452995)
          ·
            refine ⟨199110682535587752822679493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132740455023725168548452995 199110682535587752822679493)
            ·
              refine ⟨37333252975422703654252405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199110682535587752822679493 37333252975422703654252405)
              ·
                refine ⟨3499992466445878467586163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37333252975422703654252405 3499992466445878467586163)
                ·
                  refine ⟨5249988699668817701379245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499992466445878467586163 5249988699668817701379245)
                  ·
                    refine ⟨1968745762375806638017217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5249988699668817701379245 1968745762375806638017217)
                    ·
                      refine ⟨1476559321781854978512913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968745762375806638017217 1476559321781854978512913)
                      ·
                        rfl

theorem cell23_2875589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_2875589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875589 prefixEnd_2875589 := by exact prefixLift 2875589
  have htrace : WordTrace (prefixWord ++ tailWord_2875589) baseStart_2875589 baseEnd_2875589 := by
    simpa [prefixWord, tailWord_2875589, baseEnd_2875589] using wordTrace_append hprefix tailTrace_2875589
  have hstable : (prefixWord ++ tailWord_2875589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875589).length < 2 ^ (prefixWord ++ tailWord_2875589).sum := by decide
  have hdescent : baseEnd_2875589 < baseStart_2875589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875595 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 2, 6]
def baseStart_2875595 : Nat := 118140960795 + 2875595 * 2 ^ 59
def prefixEnd_2875595 : Nat := 4983230072969 + 3 ^ 40 * 2875595 * 2
def baseEnd_2875595 : Nat := 492187467555260651679295

theorem tailTrace_2875595 : CollatzResearch.WordTrace tailWord_2875595 prefixEnd_2875595 492187467555260651679295 := by
  unfold tailWord_2875595
  simp only [CollatzResearch.WordTrace]
  refine ⟨104881566017217902371644239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69921044011478601581096159 104881566017217902371644239)
  ·
    refine ⟨157322349025826853557466359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104881566017217902371644239 157322349025826853557466359)
    ·
      refine ⟨235983523538740280336199539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157322349025826853557466359 235983523538740280336199539)
      ·
        refine ⟨353975285308110420504299309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235983523538740280336199539 353975285308110420504299309)
        ·
          refine ⟨132740731990541407689112241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353975285308110420504299309 132740731990541407689112241)
          ·
            refine ⟨99555548992906055766834181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132740731990541407689112241 99555548992906055766834181)
            ·
              refine ⟨18666665436169885456281409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99555548992906055766834181 18666665436169885456281409)
              ·
                refine ⟨13999999077127414092211057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18666665436169885456281409 13999999077127414092211057)
                ·
                  refine ⟨10499999307845560569158293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13999999077127414092211057 10499999307845560569158293)
                  ·
                    refine ⟨492187467555260651679295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10499999307845560569158293 492187467555260651679295)
                    ·
                      rfl

theorem cell23_2875595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_2875595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875595 prefixEnd_2875595 := by exact prefixLift 2875595
  have htrace : WordTrace (prefixWord ++ tailWord_2875595) baseStart_2875595 baseEnd_2875595 := by
    simpa [prefixWord, tailWord_2875595, baseEnd_2875595] using wordTrace_append hprefix tailTrace_2875595
  have hstable : (prefixWord ++ tailWord_2875595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875595).length < 2 ^ (prefixWord ++ tailWord_2875595).sum := by decide
  have hdescent : baseEnd_2875595 < baseStart_2875595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875602 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2875602 : Nat := 118140960795 + 2875602 * 2 ^ 59
def prefixEnd_2875602 : Nat := 4983230072969 + 3 ^ 40 * 2875602 * 2
def baseEnd_2875602 : Nat := 1476565997030363427650353

theorem tailTrace_2875602 : CollatzResearch.WordTrace tailWord_2875602 prefixEnd_2875602 1476565997030363427650353 := by
  unfold tailWord_2875602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26220455332048135641787265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69921214218795028378099373 26220455332048135641787265)
  ·
    refine ⟨19665341499036101731340449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26220455332048135641787265 19665341499036101731340449)
    ·
      refine ⟨14749006124277076298505337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19665341499036101731340449 14749006124277076298505337)
      ·
        refine ⟨11061754593207807223879003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14749006124277076298505337 11061754593207807223879003)
        ·
          refine ⟨16592631889811710835818505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11061754593207807223879003 16592631889811710835818505)
          ·
            refine ⟨12444473917358783126863879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16592631889811710835818505 12444473917358783126863879)
            ·
              refine ⟨18666710876038174690295819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12444473917358783126863879 18666710876038174690295819)
              ·
                refine ⟨28000066314057262035443729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18666710876038174690295819 28000066314057262035443729)
                ·
                  refine ⟨21000049735542946526582797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28000066314057262035443729 21000049735542946526582797)
                  ·
                    refine ⟨7875018650828604947468549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21000049735542946526582797 7875018650828604947468549)
                    ·
                      refine ⟨1476565997030363427650353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7875018650828604947468549 1476565997030363427650353)
                      ·
                        rfl

theorem cell23_2875602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2875602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875602 prefixEnd_2875602 := by exact prefixLift 2875602
  have htrace : WordTrace (prefixWord ++ tailWord_2875602) baseStart_2875602 baseEnd_2875602 := by
    simpa [prefixWord, tailWord_2875602, baseEnd_2875602] using wordTrace_append hprefix tailTrace_2875602
  have hstable : (prefixWord ++ tailWord_2875602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875602).length < 2 ^ (prefixWord ++ tailWord_2875602).sum := by decide
  have hdescent : baseEnd_2875602 < baseStart_2875602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875625 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 7]
def baseStart_2875625 : Nat := 118140960795 + 2875625 * 2 ^ 59
def prefixEnd_2875625 : Nat := 4983230072969 + 3 ^ 40 * 2875625 * 2
def baseEnd_2875625 : Nat := 164064200787268537518083

theorem tailTrace_2875625 : CollatzResearch.WordTrace tailWord_2875625 prefixEnd_2875625 164064200787268537518083 := by
  unfold tailWord_2875625
  simp only [CollatzResearch.WordTrace]
  refine ⟨104882660207109217495236329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69921773471406144996824219 104882660207109217495236329)
  ·
    refine ⟨78661995155331913121427247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104882660207109217495236329 78661995155331913121427247)
    ·
      refine ⟨117992992732997869682140871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78661995155331913121427247 117992992732997869682140871)
      ·
        refine ⟨176989489099496804523211307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117992992732997869682140871 176989489099496804523211307)
        ·
          refine ⟨265484233649245206784816961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176989489099496804523211307 265484233649245206784816961)
          ·
            refine ⟨199113175236933905088612721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265484233649245206784816961 199113175236933905088612721)
            ·
              refine ⟨149334881427700428816459541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199113175236933905088612721 149334881427700428816459541)
              ·
                refine ⟨7000072566923457600771541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149334881427700428816459541 7000072566923457600771541)
                ·
                  refine ⟨164064200787268537518083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7000072566923457600771541 164064200787268537518083)
                  ·
                    rfl

theorem cell23_2875625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_2875625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875625 prefixEnd_2875625 := by exact prefixLift 2875625
  have htrace : WordTrace (prefixWord ++ tailWord_2875625) baseStart_2875625 baseEnd_2875625 := by
    simpa [prefixWord, tailWord_2875625, baseEnd_2875625] using wordTrace_append hprefix tailTrace_2875625
  have hstable : (prefixWord ++ tailWord_2875625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875625).length < 2 ^ (prefixWord ++ tailWord_2875625).sum := by decide
  have hdescent : baseEnd_2875625 < baseStart_2875625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875692 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2875692 : Nat := 118140960795 + 2875692 * 2 ^ 59
def prefixEnd_2875692 : Nat := 4983230072969 + 3 ^ 40 * 2875692 * 2
def baseEnd_2875692 : Nat := 1476612210289268075524939

theorem tailTrace_2875692 : CollatzResearch.WordTrace tailWord_2875692 prefixEnd_2875692 1476612210289268075524939 := by
  unfold tailWord_2875692
  simp only [CollatzResearch.WordTrace]
  refine ⟨52442551948933243968962665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69923402598577658625283553 52442551948933243968962665)
  ·
    refine ⟨39331913961699932976721999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52442551948933243968962665 39331913961699932976721999)
    ·
      refine ⟨58997870942549899465082999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39331913961699932976721999 58997870942549899465082999)
      ·
        refine ⟨88496806413824849197624499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58997870942549899465082999 88496806413824849197624499)
        ·
          refine ⟨132745209620737273796436749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88496806413824849197624499 132745209620737273796436749)
          ·
            refine ⟨49779453607776477673663781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132745209620737273796436749 49779453607776477673663781)
            ·
              refine ⟨9333647551458089563811959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49779453607776477673663781 9333647551458089563811959)
              ·
                refine ⟨14000471327187134345717939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333647551458089563811959 14000471327187134345717939)
                ·
                  refine ⟨21000706990780701518576909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14000471327187134345717939 21000706990780701518576909)
                  ·
                    refine ⟨7875265121542763069466341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21000706990780701518576909 7875265121542763069466341)
                    ·
                      refine ⟨1476612210289268075524939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7875265121542763069466341 1476612210289268075524939)
                      ·
                        rfl

theorem cell23_2875692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2875692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875692 prefixEnd_2875692 := by exact prefixLift 2875692
  have htrace : WordTrace (prefixWord ++ tailWord_2875692) baseStart_2875692 baseEnd_2875692 := by
    simpa [prefixWord, tailWord_2875692, baseEnd_2875692] using wordTrace_append hprefix tailTrace_2875692
  have hstable : (prefixWord ++ tailWord_2875692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875692).length < 2 ^ (prefixWord ++ tailWord_2875692).sum := by decide
  have hdescent : baseEnd_2875692 < baseStart_2875692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875712 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_2875712 : Nat := 118140960795 + 2875712 * 2 ^ 59
def prefixEnd_2875712 : Nat := 4983230072969 + 3 ^ 40 * 2875712 * 2
def baseEnd_2875712 : Nat := 1476622479902357997274847

theorem tailTrace_2875712 : CollatzResearch.WordTrace tailWord_2875712 prefixEnd_2875712 1476622479902357997274847 := by
  unfold tailWord_2875712
  simp only [CollatzResearch.WordTrace]
  refine ⟨52442916678897015676826695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69923888905196020902435593 52442916678897015676826695)
  ·
    refine ⟨78664375018345523515240043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52442916678897015676826695 78664375018345523515240043)
    ·
      refine ⟨117996562527518285272860065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78664375018345523515240043 117996562527518285272860065)
      ·
        refine ⟨88497421895638713954645049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117996562527518285272860065 88497421895638713954645049)
        ·
          refine ⟨66373066421729035465983787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88497421895638713954645049 66373066421729035465983787)
          ·
            refine ⟨99559599632593553198975681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66373066421729035465983787 99559599632593553198975681)
            ·
              refine ⟨74669699724445164899231761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99559599632593553198975681 74669699724445164899231761)
              ·
                refine ⟨56002274793333873674423821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74669699724445164899231761 56002274793333873674423821)
                ·
                  refine ⟨21000853047500202627908933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56002274793333873674423821 21000853047500202627908933)
                  ·
                    refine ⟨3937659946406287992732925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21000853047500202627908933 3937659946406287992732925)
                    ·
                      refine ⟨1476622479902357997274847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937659946406287992732925 1476622479902357997274847)
                      ·
                        rfl

theorem cell23_2875712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_2875712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875712 prefixEnd_2875712 := by exact prefixLift 2875712
  have htrace : WordTrace (prefixWord ++ tailWord_2875712) baseStart_2875712 baseEnd_2875712 := by
    simpa [prefixWord, tailWord_2875712, baseEnd_2875712] using wordTrace_append hprefix tailTrace_2875712
  have hstable : (prefixWord ++ tailWord_2875712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875712).length < 2 ^ (prefixWord ++ tailWord_2875712).sum := by decide
  have hdescent : baseEnd_2875712 < baseStart_2875712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875716 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2875716 : Nat := 118140960795 + 2875716 * 2 ^ 59
def prefixEnd_2875716 : Nat := 4983230072969 + 3 ^ 40 * 2875716 * 2
def baseEnd_2875716 : Nat := 1476624533824975981624829

theorem tailTrace_2875716 : CollatzResearch.WordTrace tailWord_2875716 prefixEnd_2875716 1476624533824975981624829 := by
  unfold tailWord_2875716
  simp only [CollatzResearch.WordTrace]
  refine ⟨52442989624889770018399501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69923986166519693357866001 52442989624889770018399501)
  ·
    refine ⟨19666121109333663756899813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52442989624889770018399501 19666121109333663756899813)
    ·
      refine ⟨3687397708000061954418715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19666121109333663756899813 3687397708000061954418715)
      ·
        refine ⟨5531096562000092931628073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3687397708000061954418715 5531096562000092931628073)
        ·
          refine ⟨4148322421500069698721055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5531096562000092931628073 4148322421500069698721055)
          ·
            refine ⟨6222483632250104548081583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148322421500069698721055 6222483632250104548081583)
            ·
              refine ⟨9333725448375156822122375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222483632250104548081583 9333725448375156822122375)
              ·
                refine ⟨14000588172562735233183563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333725448375156822122375 14000588172562735233183563)
                ·
                  refine ⟨21000882258844102849775345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14000588172562735233183563 21000882258844102849775345)
                  ·
                    refine ⟨15750661694133077137331509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21000882258844102849775345 15750661694133077137331509)
                    ·
                      refine ⟨1476624533824975981624829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15750661694133077137331509 1476624533824975981624829)
                      ·
                        rfl

theorem cell23_2875716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2875716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875716 prefixEnd_2875716 := by exact prefixLift 2875716
  have htrace : WordTrace (prefixWord ++ tailWord_2875716) baseStart_2875716 baseEnd_2875716 := by
    simpa [prefixWord, tailWord_2875716, baseEnd_2875716] using wordTrace_append hprefix tailTrace_2875716
  have hstable : (prefixWord ++ tailWord_2875716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875716).length < 2 ^ (prefixWord ++ tailWord_2875716).sum := by decide
  have hdescent : baseEnd_2875716 < baseStart_2875716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875746 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2875746 : Nat := 118140960795 + 2875746 * 2 ^ 59
def prefixEnd_2875746 : Nat := 4983230072969 + 3 ^ 40 * 2875746 * 2
def baseEnd_2875746 : Nat := 1476639938244610864249691

theorem tailTrace_2875746 : CollatzResearch.WordTrace tailWord_2875746 prefixEnd_2875746 1476639938244610864249691 := by
  unfold tailWord_2875746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26221768359917713790097773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69924715626447236773594061 26221768359917713790097773)
  ·
    refine ⟨9833163134969142671286665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26221768359917713790097773 9833163134969142671286665)
    ·
      refine ⟨7374872351226857003464999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9833163134969142671286665 7374872351226857003464999)
      ·
        refine ⟨11062308526840285505197499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374872351226857003464999 11062308526840285505197499)
        ·
          refine ⟨16593462790260428257796249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062308526840285505197499 16593462790260428257796249)
          ·
            refine ⟨12445097092695321193347187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16593462790260428257796249 12445097092695321193347187)
            ·
              refine ⟨18667645639042981790020781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12445097092695321193347187 18667645639042981790020781)
              ·
                refine ⟨7000367114641118171257793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18667645639042981790020781 7000367114641118171257793)
                ·
                  refine ⟨5250275335980838628443345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000367114641118171257793 5250275335980838628443345)
                  ·
                    refine ⟨3937706501985628971332509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5250275335980838628443345 3937706501985628971332509)
                    ·
                      refine ⟨1476639938244610864249691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937706501985628971332509 1476639938244610864249691)
                      ·
                        rfl

theorem cell23_2875746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2875746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875746 prefixEnd_2875746 := by exact prefixLift 2875746
  have htrace : WordTrace (prefixWord ++ tailWord_2875746) baseStart_2875746 baseEnd_2875746 := by
    simpa [prefixWord, tailWord_2875746, baseEnd_2875746] using wordTrace_append hprefix tailTrace_2875746
  have hstable : (prefixWord ++ tailWord_2875746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875746).length < 2 ^ (prefixWord ++ tailWord_2875746).sum := by decide
  have hdescent : baseEnd_2875746 < baseStart_2875746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875759 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 3]
def baseStart_2875759 : Nat := 118140960795 + 2875759 * 2 ^ 59
def prefixEnd_2875759 : Nat := 4983230072969 + 3 ^ 40 * 2875759 * 2
def baseEnd_2875759 : Nat := 1476646613493119313387131

theorem tailTrace_2875759 : CollatzResearch.WordTrace tailWord_2875759 prefixEnd_2875759 1476646613493119313387131 := by
  unfold tailWord_2875759
  simp only [CollatzResearch.WordTrace]
  refine ⟨104887547588623758380614331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69925031725749172253742887 104887547588623758380614331)
  ·
    refine ⟨157331321382935637570921497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104887547588623758380614331 157331321382935637570921497)
    ·
      refine ⟨117998491037201728178191123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157331321382935637570921497 117998491037201728178191123)
      ·
        refine ⟨176997736555802592267286685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117998491037201728178191123 176997736555802592267286685)
        ·
          refine ⟨66374151208425972100232507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176997736555802592267286685 66374151208425972100232507)
          ·
            refine ⟨99561226812638958150348761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66374151208425972100232507 99561226812638958150348761)
            ·
              refine ⟨74670920109479218612761571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99561226812638958150348761 74670920109479218612761571)
              ·
                refine ⟨112006380164218827919142357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74670920109479218612761571 112006380164218827919142357)
                ·
                  refine ⟨2625149535098878779354899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112006380164218827919142357 2625149535098878779354899)
                  ·
                    refine ⟨3937724302648318169032349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625149535098878779354899 3937724302648318169032349)
                    ·
                      refine ⟨1476646613493119313387131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937724302648318169032349 1476646613493119313387131)
                      ·
                        rfl

theorem cell23_2875759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_2875759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875759 prefixEnd_2875759 := by exact prefixLift 2875759
  have htrace : WordTrace (prefixWord ++ tailWord_2875759) baseStart_2875759 baseEnd_2875759 := by
    simpa [prefixWord, tailWord_2875759, baseEnd_2875759] using wordTrace_append hprefix tailTrace_2875759
  have hstable : (prefixWord ++ tailWord_2875759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875759).length < 2 ^ (prefixWord ++ tailWord_2875759).sum := by decide
  have hdescent : baseEnd_2875759 < baseStart_2875759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875769 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 5, 2]
def baseStart_2875769 : Nat := 118140960795 + 2875769 * 2 ^ 59
def prefixEnd_2875769 : Nat := 4983230072969 + 3 ^ 40 * 2875769 * 2
def baseEnd_2875769 : Nat := 1476651748299664274262085

theorem tailTrace_2875769 : CollatzResearch.WordTrace tailWord_2875769 prefixEnd_2875769 1476651748299664274262085 := by
  unfold tailWord_2875769
  simp only [CollatzResearch.WordTrace]
  refine ⟨104887912318587530088478361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69925274879058353392318907 104887912318587530088478361)
  ·
    refine ⟨78665934238940647566358771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104887912318587530088478361 78665934238940647566358771)
    ·
      refine ⟨117998901358410971349538157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78665934238940647566358771 117998901358410971349538157)
      ·
        refine ⟨44249588009404114256076809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117998901358410971349538157 44249588009404114256076809)
        ·
          refine ⟨33187191007053085692057607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44249588009404114256076809 33187191007053085692057607)
          ·
            refine ⟨49780786510579628538086411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33187191007053085692057607 49780786510579628538086411)
            ·
              refine ⟨74671179765869442807129617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49780786510579628538086411 74671179765869442807129617)
              ·
                refine ⟨56003384824402082105347213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74671179765869442807129617 56003384824402082105347213)
                ·
                  refine ⟨21001269309150780789505205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56003384824402082105347213 21001269309150780789505205)
                  ·
                    refine ⟨1968868997732885699016113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21001269309150780789505205 1968868997732885699016113)
                    ·
                      refine ⟨1476651748299664274262085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968868997732885699016113 1476651748299664274262085)
                      ·
                        rfl

theorem cell23_2875769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_2875769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875769 prefixEnd_2875769 := by exact prefixLift 2875769
  have htrace : WordTrace (prefixWord ++ tailWord_2875769) baseStart_2875769 baseEnd_2875769 := by
    simpa [prefixWord, tailWord_2875769, baseEnd_2875769] using wordTrace_append hprefix tailTrace_2875769
  have hstable : (prefixWord ++ tailWord_2875769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875769).length < 2 ^ (prefixWord ++ tailWord_2875769).sum := by decide
  have hdescent : baseEnd_2875769 < baseStart_2875769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875799 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2875799 : Nat := 118140960795 + 2875799 * 2 ^ 59
def prefixEnd_2875799 : Nat := 4983230072969 + 3 ^ 40 * 2875799 * 2
def baseEnd_2875799 : Nat := 1476667152719299156886947

theorem tailTrace_2875799 : CollatzResearch.WordTrace tailWord_2875799 prefixEnd_2875799 1476667152719299156886947 := by
  unfold tailWord_2875799
  simp only [CollatzResearch.WordTrace]
  refine ⟨104889006508478845212070451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69926004338985896808046967 104889006508478845212070451)
  ·
    refine ⟨157333509762718267818105677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104889006508478845212070451 157333509762718267818105677)
    ·
      refine ⟨59000066161019350431789629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157333509762718267818105677 59000066161019350431789629)
      ·
        refine ⟨22125024810382256411921111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59000066161019350431789629 22125024810382256411921111)
        ·
          refine ⟨33187537215573384617881667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22125024810382256411921111 33187537215573384617881667)
          ·
            refine ⟨49781305823360076926822501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33187537215573384617881667 49781305823360076926822501)
            ·
              refine ⟨9333994841880014423779219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49781305823360076926822501 9333994841880014423779219)
              ·
                refine ⟨14000992262820021635668829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333994841880014423779219 14000992262820021635668829)
                ·
                  refine ⟨5250372098557508113375811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14000992262820021635668829 5250372098557508113375811)
                  ·
                    refine ⟨7875558147836262170063717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5250372098557508113375811 7875558147836262170063717)
                    ·
                      refine ⟨1476667152719299156886947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7875558147836262170063717 1476667152719299156886947)
                      ·
                        rfl

theorem cell23_2875799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2875799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875799 prefixEnd_2875799 := by exact prefixLift 2875799
  have htrace : WordTrace (prefixWord ++ tailWord_2875799) baseStart_2875799 baseEnd_2875799 := by
    simpa [prefixWord, tailWord_2875799, baseEnd_2875799] using wordTrace_append hprefix tailTrace_2875799
  have hstable : (prefixWord ++ tailWord_2875799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875799).length < 2 ^ (prefixWord ++ tailWord_2875799).sum := by decide
  have hdescent : baseEnd_2875799 < baseStart_2875799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875810 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2875810 : Nat := 118140960795 + 2875810 * 2 ^ 59
def prefixEnd_2875810 : Nat := 4983230072969 + 3 ^ 40 * 2875810 * 2
def baseEnd_2875810 : Nat := 1476672801006498613849397

theorem tailTrace_2875810 : CollatzResearch.WordTrace tailWord_2875810 prefixEnd_2875810 1476672801006498613849397 := by
  unfold tailWord_2875810
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222351927859748522680221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69926271807625996060480589 26222351927859748522680221)
  ·
    refine ⟨9833381972947405696005083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26222351927859748522680221 9833381972947405696005083)
    ·
      refine ⟨14750072959421108544007625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9833381972947405696005083 14750072959421108544007625)
      ·
        refine ⟨11062554719565831408005719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14750072959421108544007625 11062554719565831408005719)
        ·
          refine ⟨16593832079348747112008579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062554719565831408005719 16593832079348747112008579)
          ·
            refine ⟨24890748119023120668012869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16593832079348747112008579 24890748119023120668012869)
            ·
              refine ⟨4667015272316835125252413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24890748119023120668012869 4667015272316835125252413)
              ·
                refine ⟨1750130727118813171969655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4667015272316835125252413 1750130727118813171969655)
                ·
                  refine ⟨2625196090678219757954483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750130727118813171969655 2625196090678219757954483)
                  ·
                    refine ⟨3937794136017329636931725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625196090678219757954483 3937794136017329636931725)
                    ·
                      refine ⟨1476672801006498613849397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937794136017329636931725 1476672801006498613849397)
                      ·
                        rfl

theorem cell23_2875810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2875810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875810 prefixEnd_2875810 := by exact prefixLift 2875810
  have htrace : WordTrace (prefixWord ++ tailWord_2875810) baseStart_2875810 baseEnd_2875810 := by
    simpa [prefixWord, tailWord_2875810, baseEnd_2875810] using wordTrace_append hprefix tailTrace_2875810
  have hstable : (prefixWord ++ tailWord_2875810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875810).length < 2 ^ (prefixWord ++ tailWord_2875810).sum := by decide
  have hdescent : baseEnd_2875810 < baseStart_2875810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875832 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_2875832 : Nat := 118140960795 + 2875832 * 2 ^ 59
def prefixEnd_2875832 : Nat := 4983230072969 + 3 ^ 40 * 2875832 * 2
def baseEnd_2875832 : Nat := 1476684097580897527774295

theorem tailTrace_2875832 : CollatzResearch.WordTrace tailWord_2875832 prefixEnd_2875832 1476684097580897527774295 := by
  unfold tailWord_2875832
  simp only [CollatzResearch.WordTrace]
  refine ⟨52445105058679645924010875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69926806744906194565347833 52445105058679645924010875)
  ·
    refine ⟨78667657588019468886016313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52445105058679645924010875 78667657588019468886016313)
    ·
      refine ⟨59000743191014601664512235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78667657588019468886016313 59000743191014601664512235)
      ·
        refine ⟨88501114786521902496768353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59000743191014601664512235 88501114786521902496768353)
        ·
          refine ⟨66375836089891426872576265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88501114786521902496768353 66375836089891426872576265)
          ·
            refine ⟨49781877067418570154432199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66375836089891426872576265 49781877067418570154432199)
            ·
              refine ⟨74672815601127855231648299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49781877067418570154432199 74672815601127855231648299)
              ·
                refine ⟨112009223401691782847472449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74672815601127855231648299 112009223401691782847472449)
                ·
                  refine ⟨84006917551268837135604337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112009223401691782847472449 84006917551268837135604337)
                  ·
                    refine ⟨63005188163451627851703253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84006917551268837135604337 63005188163451627851703253)
                    ·
                      refine ⟨1476684097580897527774295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63005188163451627851703253 1476684097580897527774295)
                      ·
                        rfl

theorem cell23_2875832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_2875832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875832 prefixEnd_2875832 := by exact prefixLift 2875832
  have htrace : WordTrace (prefixWord ++ tailWord_2875832) baseStart_2875832 baseEnd_2875832 := by
    simpa [prefixWord, tailWord_2875832, baseEnd_2875832] using wordTrace_append hprefix tailTrace_2875832
  have hstable : (prefixWord ++ tailWord_2875832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875832).length < 2 ^ (prefixWord ++ tailWord_2875832).sum := by decide
  have hdescent : baseEnd_2875832 < baseStart_2875832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875833 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 3, 2, 2]
def baseStart_2875833 : Nat := 118140960795 + 2875833 * 2 ^ 59
def prefixEnd_2875833 : Nat := 4983230072969 + 3 ^ 40 * 2875833 * 2
def baseEnd_2875833 : Nat := 1476684611061552023861791

theorem tailTrace_2875833 : CollatzResearch.WordTrace tailWord_2875833 prefixEnd_2875833 1476684611061552023861791 := by
  unfold tailWord_2875833
  simp only [CollatzResearch.WordTrace]
  refine ⟨104890246590355669018808153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69926831060237112679205435 104890246590355669018808153)
  ·
    refine ⟨78667684942766751764106115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104890246590355669018808153 78667684942766751764106115)
    ·
      refine ⟨118001527414150127646159173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78667684942766751764106115 118001527414150127646159173)
      ·
        refine ⟨22125286390153148933654845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118001527414150127646159173 22125286390153148933654845)
        ·
          refine ⟨8296982396307430850120567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22125286390153148933654845 8296982396307430850120567)
          ·
            refine ⟨12445473594461146275180851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8296982396307430850120567 12445473594461146275180851)
            ·
              refine ⟨18668210391691719412771277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12445473594461146275180851 18668210391691719412771277)
              ·
                refine ⟨7000578896884394779789229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18668210391691719412771277 7000578896884394779789229)
                ·
                  refine ⟨2625217086331648042420961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7000578896884394779789229 2625217086331648042420961)
                  ·
                    refine ⟨1968912814748736031815721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2625217086331648042420961 1968912814748736031815721)
                    ·
                      refine ⟨1476684611061552023861791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968912814748736031815721 1476684611061552023861791)
                      ·
                        rfl

theorem cell23_2875833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_2875833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875833 prefixEnd_2875833 := by exact prefixLift 2875833
  have htrace : WordTrace (prefixWord ++ tailWord_2875833) baseStart_2875833 baseEnd_2875833 := by
    simpa [prefixWord, tailWord_2875833, baseEnd_2875833] using wordTrace_append hprefix tailTrace_2875833
  have hstable : (prefixWord ++ tailWord_2875833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875833).length < 2 ^ (prefixWord ++ tailWord_2875833).sum := by decide
  have hdescent : baseEnd_2875833 < baseStart_2875833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875836 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2875836 : Nat := 118140960795 + 2875836 * 2 ^ 59
def prefixEnd_2875836 : Nat := 4983230072969 + 3 ^ 40 * 2875836 * 2
def baseEnd_2875836 : Nat := 1476686151503515512124277

theorem tailTrace_2875836 : CollatzResearch.WordTrace tailWord_2875836 prefixEnd_2875836 1476686151503515512124277 := by
  unfold tailWord_2875836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52445178004672400265583681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69926904006229867020778241 52445178004672400265583681)
  ·
    refine ⟨39333883503504300199187761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52445178004672400265583681 39333883503504300199187761)
    ·
      refine ⟨29500412627628225149390821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39333883503504300199187761 29500412627628225149390821)
      ·
        refine ⟨5531327367680292215510779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29500412627628225149390821 5531327367680292215510779)
        ·
          refine ⟨8296991051520438323266169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5531327367680292215510779 8296991051520438323266169)
          ·
            refine ⟨6222743288640328742449627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8296991051520438323266169 6222743288640328742449627)
            ·
              refine ⟨9334114932960493113674441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222743288640328742449627 9334114932960493113674441)
              ·
                refine ⟨7000586199720369835255831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9334114932960493113674441 7000586199720369835255831)
                ·
                  refine ⟨10500879299580554752883747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7000586199720369835255831 10500879299580554752883747)
                  ·
                    refine ⟨15751318949370832129325621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10500879299580554752883747 15751318949370832129325621)
                    ·
                      refine ⟨1476686151503515512124277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15751318949370832129325621 1476686151503515512124277)
                      ·
                        rfl

theorem cell23_2875836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2875836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875836 prefixEnd_2875836 := by exact prefixLift 2875836
  have htrace : WordTrace (prefixWord ++ tailWord_2875836) baseStart_2875836 baseEnd_2875836 := by
    simpa [prefixWord, tailWord_2875836, baseEnd_2875836] using wordTrace_append hprefix tailTrace_2875836
  have hstable : (prefixWord ++ tailWord_2875836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875836).length < 2 ^ (prefixWord ++ tailWord_2875836).sum := by decide
  have hdescent : baseEnd_2875836 < baseStart_2875836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875866 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_2875866 : Nat := 118140960795 + 2875866 * 2 ^ 59
def prefixEnd_2875866 : Nat := 4983230072969 + 3 ^ 40 * 2875866 * 2
def baseEnd_2875866 : Nat := 1476701555923150394749139

theorem tailTrace_2875866 : CollatzResearch.WordTrace tailWord_2875866 prefixEnd_2875866 1476701555923150394749139 := by
  unfold tailWord_2875866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222862549809028913689863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69927633466157410436506301 26222862549809028913689863)
  ·
    refine ⟨39334293824713543370534795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26222862549809028913689863 39334293824713543370534795)
    ·
      refine ⟨59001440737070315055802193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39334293824713543370534795 59001440737070315055802193)
      ·
        refine ⟨44251080552802736291851645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59001440737070315055802193 44251080552802736291851645)
        ·
          refine ⟨16594155207301026109444367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44251080552802736291851645 16594155207301026109444367)
          ·
            refine ⟨24891232810951539164166551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594155207301026109444367 24891232810951539164166551)
            ·
              refine ⟨37336849216427308746249827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24891232810951539164166551 37336849216427308746249827)
              ·
                refine ⟨56005273824640963119374741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37336849216427308746249827 56005273824640963119374741)
                ·
                  refine ⟨2625247210530045146220691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56005273824640963119374741 2625247210530045146220691)
                  ·
                    refine ⟨3937870815795067719331037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625247210530045146220691 3937870815795067719331037)
                    ·
                      refine ⟨1476701555923150394749139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3937870815795067719331037 1476701555923150394749139)
                      ·
                        rfl

theorem cell23_2875866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_2875866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875866 prefixEnd_2875866 := by exact prefixLift 2875866
  have htrace : WordTrace (prefixWord ++ tailWord_2875866) baseStart_2875866 baseEnd_2875866 := by
    simpa [prefixWord, tailWord_2875866, baseEnd_2875866] using wordTrace_append hprefix tailTrace_2875866
  have hstable : (prefixWord ++ tailWord_2875866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875866).length < 2 ^ (prefixWord ++ tailWord_2875866).sum := by decide
  have hdescent : baseEnd_2875866 < baseStart_2875866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875876 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_2875876 : Nat := 118140960795 + 2875876 * 2 ^ 59
def prefixEnd_2875876 : Nat := 4983230072969 + 3 ^ 40 * 2875876 * 2
def baseEnd_2875876 : Nat := 1476706690729695355624093

theorem tailTrace_2875876 : CollatzResearch.WordTrace tailWord_2875876 prefixEnd_2875876 1476706690729695355624093 := by
  unfold tailWord_2875876
  simp only [CollatzResearch.WordTrace]
  refine ⟨52445907464599943681311741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69927876619466591575082321 52445907464599943681311741)
  ·
    refine ⟨19667215299224978880491903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52445907464599943681311741 19667215299224978880491903)
    ·
      refine ⟨29500822948837468320737855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19667215299224978880491903 29500822948837468320737855)
      ·
        refine ⟨44251234423256202481106783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29500822948837468320737855 44251234423256202481106783)
        ·
          refine ⟨66376851634884303721660175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44251234423256202481106783 66376851634884303721660175)
          ·
            refine ⟨99565277452326455582490263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66376851634884303721660175 99565277452326455582490263)
            ·
              refine ⟨149347916178489683373735395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99565277452326455582490263 149347916178489683373735395)
              ·
                refine ⟨224021874267734525060603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149347916178489683373735395 224021874267734525060603093)
                ·
                  refine ⟨5250512678150027931107885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224021874267734525060603093 5250512678150027931107885)
                  ·
                    refine ⟨1968942254306260474165457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5250512678150027931107885 1968942254306260474165457)
                    ·
                      refine ⟨1476706690729695355624093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1968942254306260474165457 1476706690729695355624093)
                      ·
                        rfl

theorem cell23_2875876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_2875876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875876 prefixEnd_2875876 := by exact prefixLift 2875876
  have htrace : WordTrace (prefixWord ++ tailWord_2875876) baseStart_2875876 baseEnd_2875876 := by
    simpa [prefixWord, tailWord_2875876, baseEnd_2875876] using wordTrace_append hprefix tailTrace_2875876
  have hstable : (prefixWord ++ tailWord_2875876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875876).length < 2 ^ (prefixWord ++ tailWord_2875876).sum := by decide
  have hdescent : baseEnd_2875876 < baseStart_2875876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875879 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2875879 : Nat := 118140960795 + 2875879 * 2 ^ 59
def prefixEnd_2875879 : Nat := 4983230072969 + 3 ^ 40 * 2875879 * 2
def baseEnd_2875879 : Nat := 1476708231171658843886579

theorem tailTrace_2875879 : CollatzResearch.WordTrace tailWord_2875879 prefixEnd_2875879 1476708231171658843886579 := by
  unfold tailWord_2875879
  simp only [CollatzResearch.WordTrace]
  refine ⟨104891924348189018874982691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69927949565459345916655127 104891924348189018874982691)
  ·
    refine ⟨157337886522283528312474037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104891924348189018874982691 157337886522283528312474037)
    ·
      refine ⟨14750426861464080779294441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157337886522283528312474037 14750426861464080779294441)
      ·
        refine ⟨11062820146098060584470831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14750426861464080779294441 11062820146098060584470831)
        ·
          refine ⟨16594230219147090876706247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062820146098060584470831 16594230219147090876706247)
          ·
            refine ⟨24891345328720636315059371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594230219147090876706247 24891345328720636315059371)
            ·
              refine ⟨37337017993080954472589057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24891345328720636315059371 37337017993080954472589057)
              ·
                refine ⟨28002763494810715854441793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37337017993080954472589057 28002763494810715854441793)
                ·
                  refine ⟨21002072621108036890831345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28002763494810715854441793 21002072621108036890831345)
                  ·
                    refine ⟨15751554465831027668123509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21002072621108036890831345 15751554465831027668123509)
                    ·
                      refine ⟨1476708231171658843886579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15751554465831027668123509 1476708231171658843886579)
                      ·
                        rfl

theorem cell23_2875879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2875879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875879 prefixEnd_2875879 := by exact prefixLift 2875879
  have htrace : WordTrace (prefixWord ++ tailWord_2875879) baseStart_2875879 baseEnd_2875879 := by
    simpa [prefixWord, tailWord_2875879, baseEnd_2875879] using wordTrace_append hprefix tailTrace_2875879
  have hstable : (prefixWord ++ tailWord_2875879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875879).length < 2 ^ (prefixWord ++ tailWord_2875879).sum := by decide
  have hdescent : baseEnd_2875879 < baseStart_2875879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875889 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2875889 : Nat := 118140960795 + 2875889 * 2 ^ 59
def prefixEnd_2875889 : Nat := 4983230072969 + 3 ^ 40 * 2875889 * 2
def baseEnd_2875889 : Nat := 1476713365978203804761533

theorem tailTrace_2875889 : CollatzResearch.WordTrace tailWord_2875889 prefixEnd_2875889 1476713365978203804761533 := by
  unfold tailWord_2875889
  simp only [CollatzResearch.WordTrace]
  refine ⟨104892289078152790582846721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69928192718768527055231147 104892289078152790582846721)
  ·
    refine ⟨78669216808614592937135041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104892289078152790582846721 78669216808614592937135041)
    ·
      refine ⟨59001912606460944702851281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78669216808614592937135041 59001912606460944702851281)
      ·
        refine ⟨44251434454845708527138461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59001912606460944702851281 44251434454845708527138461)
        ·
          refine ⟨16594287920567140697676923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44251434454845708527138461 16594287920567140697676923)
          ·
            refine ⟨24891431880850711046515385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594287920567140697676923 24891431880850711046515385)
            ·
              refine ⟨18668573910638033284886539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24891431880850711046515385 18668573910638033284886539)
              ·
                refine ⟨28002860865957049927329809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18668573910638033284886539 28002860865957049927329809)
                ·
                  refine ⟨21002145649467787445497357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28002860865957049927329809 21002145649467787445497357)
                  ·
                    refine ⟨7875804618550420292061509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21002145649467787445497357 7875804618550420292061509)
                    ·
                      refine ⟨1476713365978203804761533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7875804618550420292061509 1476713365978203804761533)
                      ·
                        rfl

theorem cell23_2875889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2875889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875889 prefixEnd_2875889 := by exact prefixLift 2875889
  have htrace : WordTrace (prefixWord ++ tailWord_2875889) baseStart_2875889 baseEnd_2875889 := by
    simpa [prefixWord, tailWord_2875889, baseEnd_2875889] using wordTrace_append hprefix tailTrace_2875889
  have hstable : (prefixWord ++ tailWord_2875889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875889).length < 2 ^ (prefixWord ++ tailWord_2875889).sum := by decide
  have hdescent : baseEnd_2875889 < baseStart_2875889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875909 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2875909 : Nat := 118140960795 + 2875909 * 2 ^ 59
def prefixEnd_2875909 : Nat := 4983230072969 + 3 ^ 40 * 2875909 * 2
def baseEnd_2875909 : Nat := 1476723635591293726511441

theorem tailTrace_2875909 : CollatzResearch.WordTrace tailWord_2875909 prefixEnd_2875909 1476723635591293726511441 := by
  unfold tailWord_2875909
  simp only [CollatzResearch.WordTrace]
  refine ⟨104893018538080333998574781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69928679025386889332383187 104893018538080333998574781)
  ·
    refine ⟨39334881951780125249465543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104893018538080333998574781 39334881951780125249465543)
    ·
      refine ⟨59002322927670187874198315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39334881951780125249465543 59002322927670187874198315)
      ·
        refine ⟨88503484391505281811297473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59002322927670187874198315 88503484391505281811297473)
        ·
          refine ⟨66377613293628961358473105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88503484391505281811297473 66377613293628961358473105)
          ·
            refine ⟨49783209970221721018854829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66377613293628961358473105 49783209970221721018854829)
            ·
              refine ⟨18668703738833145382070561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49783209970221721018854829 18668703738833145382070561)
              ·
                refine ⟨14001527804124859036552921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18668703738833145382070561 14001527804124859036552921)
                ·
                  refine ⟨10501145853093644277414691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14001527804124859036552921 10501145853093644277414691)
                  ·
                    refine ⟨15751718779640466416122037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10501145853093644277414691 15751718779640466416122037)
                    ·
                      refine ⟨1476723635591293726511441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15751718779640466416122037 1476723635591293726511441)
                      ·
                        rfl

theorem cell23_2875909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2875909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875909 prefixEnd_2875909 := by exact prefixLift 2875909
  have htrace : WordTrace (prefixWord ++ tailWord_2875909) baseStart_2875909 baseEnd_2875909 := by
    simpa [prefixWord, tailWord_2875909, baseEnd_2875909] using wordTrace_append hprefix tailTrace_2875909
  have hstable : (prefixWord ++ tailWord_2875909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875909).length < 2 ^ (prefixWord ++ tailWord_2875909).sum := by decide
  have hdescent : baseEnd_2875909 < baseStart_2875909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875959 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 7]
def baseStart_2875959 : Nat := 118140960795 + 2875959 * 2 ^ 59
def prefixEnd_2875959 : Nat := 4983230072969 + 3 ^ 40 * 2875959 * 2
def baseEnd_2875959 : Nat := 492249769874672843628737

theorem tailTrace_2875959 : CollatzResearch.WordTrace tailWord_2875959 prefixEnd_2875959 492249769874672843628737 := by
  unfold tailWord_2875959
  simp only [CollatzResearch.WordTrace]
  refine ⟨104894842187899192537894931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69929894791932795025263287 104894842187899192537894931)
  ·
    refine ⟨157342263281848788806842397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104894842187899192537894931 157342263281848788806842397)
    ·
      refine ⟨59003348730693295802565899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157342263281848788806842397 59003348730693295802565899)
      ·
        refine ⟨88505023096039943703848849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59003348730693295802565899 88505023096039943703848849)
        ·
          refine ⟨66378767322029957777886637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88505023096039943703848849 66378767322029957777886637)
          ·
            refine ⟨24892037745761234166707489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66378767322029957777886637 24892037745761234166707489)
            ·
              refine ⟨18669028309320925625030617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24892037745761234166707489 18669028309320925625030617)
              ·
                refine ⟨14001771231990694218772963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18669028309320925625030617 14001771231990694218772963)
                ·
                  refine ⟨21002656847986041328159445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14001771231990694218772963 21002656847986041328159445)
                  ·
                    refine ⟨492249769874672843628737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21002656847986041328159445 492249769874672843628737)
                    ·
                      rfl

theorem cell23_2875959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_2875959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875959 prefixEnd_2875959 := by exact prefixLift 2875959
  have htrace : WordTrace (prefixWord ++ tailWord_2875959) baseStart_2875959 baseEnd_2875959 := by
    simpa [prefixWord, tailWord_2875959, baseEnd_2875959] using wordTrace_append hprefix tailTrace_2875959
  have hstable : (prefixWord ++ tailWord_2875959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875959).length < 2 ^ (prefixWord ++ tailWord_2875959).sum := by decide
  have hdescent : baseEnd_2875959 < baseStart_2875959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875999 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2875999 : Nat := 118140960795 + 2875999 * 2 ^ 59
def prefixEnd_2875999 : Nat := 4983230072969 + 3 ^ 40 * 2875999 * 2
def baseEnd_2875999 : Nat := 1476769848850198374386027

theorem tailTrace_2875999 : CollatzResearch.WordTrace tailWord_2875999 prefixEnd_2875999 1476769848850198374386027 := by
  unfold tailWord_2875999
  simp only [CollatzResearch.WordTrace]
  refine ⟨104896301107754279369351051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69930867405169519579567367 104896301107754279369351051)
  ·
    refine ⟨157344451661631419054026577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104896301107754279369351051 157344451661631419054026577)
    ·
      refine ⟨118008338746223564290519933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157344451661631419054026577 118008338746223564290519933)
      ·
        refine ⟨44253127029833836608944975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118008338746223564290519933 44253127029833836608944975)
        ·
          refine ⟨66379690544750754913417463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44253127029833836608944975 66379690544750754913417463)
          ·
            refine ⟨99569535817126132370126195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66379690544750754913417463 99569535817126132370126195)
            ·
              refine ⟨149354303725689198555189293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99569535817126132370126195 149354303725689198555189293)
              ·
                refine ⟨56007863897133449458195985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149354303725689198555189293 56007863897133449458195985)
                ·
                  refine ⟨42005897922850087093646989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56007863897133449458195985 42005897922850087093646989)
                  ·
                    refine ⟨15752211721068782660117621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42005897922850087093646989 15752211721068782660117621)
                    ·
                      refine ⟨1476769848850198374386027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15752211721068782660117621 1476769848850198374386027)
                      ·
                        rfl

theorem cell23_2875999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2875999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2875999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2875999 prefixEnd_2875999 := by exact prefixLift 2875999
  have htrace : WordTrace (prefixWord ++ tailWord_2875999) baseStart_2875999 baseEnd_2875999 := by
    simpa [prefixWord, tailWord_2875999, baseEnd_2875999] using wordTrace_append hprefix tailTrace_2875999
  have hstable : (prefixWord ++ tailWord_2875999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875999).length < 2 ^ (prefixWord ++ tailWord_2875999).sum := by decide
  have hdescent : baseEnd_2875999 < baseStart_2875999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876009 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_2876009 : Nat := 118140960795 + 2876009 * 2 ^ 59
def prefixEnd_2876009 : Nat := 4983230072969 + 3 ^ 40 * 2876009 * 2
def baseEnd_2876009 : Nat := 1476774983656743335260981

theorem tailTrace_2876009 : CollatzResearch.WordTrace tailWord_2876009 prefixEnd_2876009 1476774983656743335260981 := by
  unfold tailWord_2876009
  simp only [CollatzResearch.WordTrace]
  refine ⟨104896665837718051077215081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69931110558478700718143387 104896665837718051077215081)
  ·
    refine ⟨78672499378288538307911311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104896665837718051077215081 78672499378288538307911311)
    ·
      refine ⟨118008749067432807461866967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78672499378288538307911311 118008749067432807461866967)
      ·
        refine ⟨177013123601149211192800451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118008749067432807461866967 177013123601149211192800451)
        ·
          refine ⟨265519685401723816789200677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177013123601149211192800451 265519685401723816789200677)
          ·
            refine ⟨49784941012823215647975127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265519685401723816789200677 49784941012823215647975127)
            ·
              refine ⟨74677411519234823471962691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49784941012823215647975127 74677411519234823471962691)
              ·
                refine ⟨112016117278852235207944037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74677411519234823471962691 112016117278852235207944037)
                ·
                  refine ⟨21003021989784794101489507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112016117278852235207944037 21003021989784794101489507)
                  ·
                    refine ⟨31504532984677191152234261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21003021989784794101489507 31504532984677191152234261)
                    ·
                      refine ⟨1476774983656743335260981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31504532984677191152234261 1476774983656743335260981)
                      ·
                        rfl

theorem cell23_2876009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_2876009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876009 prefixEnd_2876009 := by exact prefixLift 2876009
  have htrace : WordTrace (prefixWord ++ tailWord_2876009) baseStart_2876009 baseEnd_2876009 := by
    simpa [prefixWord, tailWord_2876009, baseEnd_2876009] using wordTrace_append hprefix tailTrace_2876009
  have hstable : (prefixWord ++ tailWord_2876009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876009).length < 2 ^ (prefixWord ++ tailWord_2876009).sum := by decide
  have hdescent : baseEnd_2876009 < baseStart_2876009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876033 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2876033 : Nat := 118140960795 + 2876033 * 2 ^ 59
def prefixEnd_2876033 : Nat := 4983230072969 + 3 ^ 40 * 2876033 * 2
def baseEnd_2876033 : Nat := 1476787307192451241360871

theorem tailTrace_2876033 : CollatzResearch.WordTrace tailWord_2876033 prefixEnd_2876033 1476787307192451241360871 := by
  unfold tailWord_2876033
  simp only [CollatzResearch.WordTrace]
  refine ⟨104897541189631103176088753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69931694126420735450725835 104897541189631103176088753)
  ·
    refine ⟨78673155892223327382066565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104897541189631103176088753 78673155892223327382066565)
    ·
      refine ⟨14751216729791873884137481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78673155892223327382066565 14751216729791873884137481)
      ·
        refine ⟨11063412547343905413103111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14751216729791873884137481 11063412547343905413103111)
        ·
          refine ⟨16595118821015858119654667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11063412547343905413103111 16595118821015858119654667)
          ·
            refine ⟨24892678231523787179482001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16595118821015858119654667 24892678231523787179482001)
            ·
              refine ⟨18669508673642840384611501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24892678231523787179482001 18669508673642840384611501)
              ·
                refine ⟨7001065752616065144229313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18669508673642840384611501 7001065752616065144229313)
                ·
                  refine ⟨5250799314462048858171985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7001065752616065144229313 5250799314462048858171985)
                  ·
                    refine ⟨3938099485846536643628989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5250799314462048858171985 3938099485846536643628989)
                    ·
                      refine ⟨1476787307192451241360871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938099485846536643628989 1476787307192451241360871)
                      ·
                        rfl

theorem cell23_2876033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2876033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876033 prefixEnd_2876033 := by exact prefixLift 2876033
  have htrace : WordTrace (prefixWord ++ tailWord_2876033) baseStart_2876033 baseEnd_2876033 := by
    simpa [prefixWord, tailWord_2876033, baseEnd_2876033] using wordTrace_append hprefix tailTrace_2876033
  have hstable : (prefixWord ++ tailWord_2876033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876033).length < 2 ^ (prefixWord ++ tailWord_2876033).sum := by decide
  have hdescent : baseEnd_2876033 < baseStart_2876033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876036 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 8]
def baseStart_2876036 : Nat := 118140960795 + 2876036 * 2 ^ 59
def prefixEnd_2876036 : Nat := 4983230072969 + 3 ^ 40 * 2876036 * 2
def baseEnd_2876036 : Nat := 164087649737157192180373

theorem tailTrace_2876036 : CollatzResearch.WordTrace tailWord_2876036 prefixEnd_2876036 164087649737157192180373 := by
  unfold tailWord_2876036
  simp only [CollatzResearch.WordTrace]
  refine ⟨52448825304310117344223981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69931767072413489792298641 52448825304310117344223981)
  ·
    refine ⟨19668309489116294004083993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52448825304310117344223981 19668309489116294004083993)
    ·
      refine ⟨14751232116837220503062995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19668309489116294004083993 14751232116837220503062995)
      ·
        refine ⟨22126848175255830754594493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14751232116837220503062995 22126848175255830754594493)
        ·
          refine ⟨8297568065720936532972935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22126848175255830754594493 8297568065720936532972935)
          ·
            refine ⟨12446352098581404799459403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8297568065720936532972935 12446352098581404799459403)
            ·
              refine ⟨18669528147872107199189105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446352098581404799459403 18669528147872107199189105)
              ·
                refine ⟨14002146110904080399391829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18669528147872107199189105 14002146110904080399391829)
                ·
                  refine ⟨164087649737157192180373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14002146110904080399391829 164087649737157192180373)
                  ·
                    rfl

theorem cell23_2876036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_2876036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876036 prefixEnd_2876036 := by exact prefixLift 2876036
  have htrace : WordTrace (prefixWord ++ tailWord_2876036) baseStart_2876036 baseEnd_2876036 := by
    simpa [prefixWord, tailWord_2876036, baseEnd_2876036] using wordTrace_append hprefix tailTrace_2876036
  have hstable : (prefixWord ++ tailWord_2876036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876036).length < 2 ^ (prefixWord ++ tailWord_2876036).sum := by decide
  have hdescent : baseEnd_2876036 < baseStart_2876036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876049 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_2876049 : Nat := 118140960795 + 2876049 * 2 ^ 59
def prefixEnd_2876049 : Nat := 4983230072969 + 3 ^ 40 * 2876049 * 2
def baseEnd_2876049 : Nat := 492265174294307726253599

theorem tailTrace_2876049 : CollatzResearch.WordTrace tailWord_2876049 prefixEnd_2876049 492265174294307726253599 := by
  unfold tailWord_2876049
  simp only [CollatzResearch.WordTrace]
  refine ⟨104898124757573137908671201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69932083171715425272447467 104898124757573137908671201)
  ·
    refine ⟨78673593568179853431503401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104898124757573137908671201 78673593568179853431503401)
    ·
      refine ⟨59005195176134890073627551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78673593568179853431503401 59005195176134890073627551)
      ·
        refine ⟨88507792764202335110441327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59005195176134890073627551 88507792764202335110441327)
        ·
          refine ⟨132761689146303502665661991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88507792764202335110441327 132761689146303502665661991)
          ·
            refine ⟨199142533719455253998492987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132761689146303502665661991 199142533719455253998492987)
            ·
              refine ⟨298713800579182880997739481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199142533719455253998492987 298713800579182880997739481)
              ·
                refine ⟨224035350434387160748304611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298713800579182880997739481 224035350434387160748304611)
                ·
                  refine ⟨336053025651580741122456917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224035350434387160748304611 336053025651580741122456917)
                  ·
                    refine ⟨492265174294307726253599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 336053025651580741122456917 492265174294307726253599)
                    ·
                      rfl

theorem cell23_2876049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_2876049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876049 prefixEnd_2876049 := by exact prefixLift 2876049
  have htrace : WordTrace (prefixWord ++ tailWord_2876049) baseStart_2876049 baseEnd_2876049 := by
    simpa [prefixWord, tailWord_2876049, baseEnd_2876049] using wordTrace_append hprefix tailTrace_2876049
  have hstable : (prefixWord ++ tailWord_2876049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876049).length < 2 ^ (prefixWord ++ tailWord_2876049).sum := by decide
  have hdescent : baseEnd_2876049 < baseStart_2876049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876050 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2876050 : Nat := 118140960795 + 2876050 * 2 ^ 59
def prefixEnd_2876050 : Nat := 4983230072969 + 3 ^ 40 * 2876050 * 2
def baseEnd_2876050 : Nat := 1476796036363577674848293

theorem tailTrace_2876050 : CollatzResearch.WordTrace tailWord_2876050 prefixEnd_2876050 1476796036363577674848293 := by
  unfold tailWord_2876050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224540307642378769864401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69932107487046343386305069 26224540307642378769864401)
  ·
    refine ⟨19668405230731784077398301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26224540307642378769864401 19668405230731784077398301)
    ·
      refine ⟨7375651961524419029024363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19668405230731784077398301 7375651961524419029024363)
      ·
        refine ⟨11063477942286628543536545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7375651961524419029024363 11063477942286628543536545)
        ·
          refine ⟨8297608456714971407652409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11063477942286628543536545 8297608456714971407652409)
          ·
            refine ⟨6223206342536228555739307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8297608456714971407652409 6223206342536228555739307)
            ·
              refine ⟨9334809513804342833608961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223206342536228555739307 9334809513804342833608961)
              ·
                refine ⟨7001107135353257125206721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9334809513804342833608961 7001107135353257125206721)
                ·
                  refine ⟨5250830351514942843905041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7001107135353257125206721 5250830351514942843905041)
                  ·
                    refine ⟨3938122763636207132928781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5250830351514942843905041 3938122763636207132928781)
                    ·
                      refine ⟨1476796036363577674848293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938122763636207132928781 1476796036363577674848293)
                      ·
                        rfl

theorem cell23_2876050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2876050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876050 prefixEnd_2876050 := by exact prefixLift 2876050
  have htrace : WordTrace (prefixWord ++ tailWord_2876050) baseStart_2876050 baseEnd_2876050 := by
    simpa [prefixWord, tailWord_2876050, baseEnd_2876050] using wordTrace_append hprefix tailTrace_2876050
  have hstable : (prefixWord ++ tailWord_2876050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876050).length < 2 ^ (prefixWord ++ tailWord_2876050).sum := by decide
  have hdescent : baseEnd_2876050 < baseStart_2876050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876059 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_2876059 : Nat := 118140960795 + 2876059 * 2 ^ 59
def prefixEnd_2876059 : Nat := 4983230072969 + 3 ^ 40 * 2876059 * 2
def baseEnd_2876059 : Nat := 1476800657689468139635751

theorem tailTrace_2876059 : CollatzResearch.WordTrace tailWord_2876059 prefixEnd_2876059 1476800657689468139635751 := by
  unfold tailWord_2876059
  simp only [CollatzResearch.WordTrace]
  refine ⟨104898489487536909616535231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69932326325024606411023487 104898489487536909616535231)
  ·
    refine ⟨157347734231305364424802847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104898489487536909616535231 157347734231305364424802847)
    ·
      refine ⟨236021601346958046637204271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157347734231305364424802847 236021601346958046637204271)
      ·
        refine ⟨354032402020437069955806407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236021601346958046637204271 354032402020437069955806407)
        ·
          refine ⟨531048603030655604933709611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354032402020437069955806407 531048603030655604933709611)
          ·
            refine ⟨796572904545983407400564417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531048603030655604933709611 796572904545983407400564417)
            ·
              refine ⟨597429678409487555550423313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796572904545983407400564417 597429678409487555550423313)
              ·
                refine ⟨448072258807115666662817485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597429678409487555550423313 448072258807115666662817485)
                ·
                  refine ⟨168027097052668374998556557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448072258807115666662817485 168027097052668374998556557)
                  ·
                    refine ⟨63010161394750640624458709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168027097052668374998556557 63010161394750640624458709)
                    ·
                      refine ⟨1476800657689468139635751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63010161394750640624458709 1476800657689468139635751)
                      ·
                        rfl

theorem cell23_2876059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_2876059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876059 prefixEnd_2876059 := by exact prefixLift 2876059
  have htrace : WordTrace (prefixWord ++ tailWord_2876059) baseStart_2876059 baseEnd_2876059 := by
    simpa [prefixWord, tailWord_2876059, baseEnd_2876059] using wordTrace_append hprefix tailTrace_2876059
  have hstable : (prefixWord ++ tailWord_2876059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876059).length < 2 ^ (prefixWord ++ tailWord_2876059).sum := by decide
  have hdescent : baseEnd_2876059 < baseStart_2876059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876083 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 1, 5]
def baseStart_2876083 : Nat := 118140960795 + 2876083 * 2 ^ 59
def prefixEnd_2876083 : Nat := 4983230072969 + 3 ^ 40 * 2876083 * 2
def baseEnd_2876083 : Nat := 492270993741725348578547

theorem tailTrace_2876083 : CollatzResearch.WordTrace tailWord_2876083 prefixEnd_2876083 492270993741725348578547 := by
  unfold tailWord_2876083
  simp only [CollatzResearch.WordTrace]
  refine ⟨104899364839449961715408903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69932909892966641143605935 104899364839449961715408903)
  ·
    refine ⟨157349047259174942573113355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104899364839449961715408903 157349047259174942573113355)
    ·
      refine ⟨236023570888762413859670033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157349047259174942573113355 236023570888762413859670033)
      ·
        refine ⟨177017678166571810394752525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236023570888762413859670033 177017678166571810394752525)
        ·
          refine ⟨66381629312464428898032197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177017678166571810394752525 66381629312464428898032197)
          ·
            refine ⟨12446555496087080418381037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66381629312464428898032197 12446555496087080418381037)
            ·
              refine ⟨4667458311032655156892889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12446555496087080418381037 4667458311032655156892889)
              ·
                refine ⟨3500593733274491367669667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667458311032655156892889 3500593733274491367669667)
                ·
                  refine ⟨5250890599911737051504501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500593733274491367669667 5250890599911737051504501)
                  ·
                    refine ⟨492270993741725348578547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5250890599911737051504501 492270993741725348578547)
                    ·
                      rfl

theorem cell23_2876083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 5].length) (baseStart_2876083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876083 prefixEnd_2876083 := by exact prefixLift 2876083
  have htrace : WordTrace (prefixWord ++ tailWord_2876083) baseStart_2876083 baseEnd_2876083 := by
    simpa [prefixWord, tailWord_2876083, baseEnd_2876083] using wordTrace_append hprefix tailTrace_2876083
  have hstable : (prefixWord ++ tailWord_2876083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876083).length < 2 ^ (prefixWord ++ tailWord_2876083).sum := by decide
  have hdescent : baseEnd_2876083 < baseStart_2876083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876090 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_2876090 : Nat := 118140960795 + 2876090 * 2 ^ 59
def prefixEnd_2876090 : Nat := 4983230072969 + 3 ^ 40 * 2876090 * 2
def baseEnd_2876090 : Nat := 1476816575589757518348109

theorem tailTrace_2876090 : CollatzResearch.WordTrace tailWord_2876090 prefixEnd_2876090 1476816575589757518348109 := by
  unfold tailWord_2876090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224905037606150477728431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69933080100283067940609149 26224905037606150477728431)
  ·
    refine ⟨39337357556409225716592647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26224905037606150477728431 39337357556409225716592647)
    ·
      refine ⟨59006036334613838574888971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39337357556409225716592647 59006036334613838574888971)
      ·
        refine ⟨88509054501920757862333457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59006036334613838574888971 88509054501920757862333457)
        ·
          refine ⟨66381790876440568396750093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88509054501920757862333457 66381790876440568396750093)
          ·
            refine ⟨24893171578665213148781285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66381790876440568396750093 24893171578665213148781285)
            ·
              refine ⟨4667469670999727465396491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24893171578665213148781285 4667469670999727465396491)
              ·
                refine ⟨7001204506499591198094737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667469670999727465396491 7001204506499591198094737)
                ·
                  refine ⟨5250903379874693398571053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7001204506499591198094737 5250903379874693398571053)
                  ·
                    refine ⟨1969088767453010024464145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5250903379874693398571053 1969088767453010024464145)
                    ·
                      refine ⟨1476816575589757518348109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969088767453010024464145 1476816575589757518348109)
                      ·
                        rfl

theorem cell23_2876090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_2876090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876090 prefixEnd_2876090 := by exact prefixLift 2876090
  have htrace : WordTrace (prefixWord ++ tailWord_2876090) baseStart_2876090 baseEnd_2876090 := by
    simpa [prefixWord, tailWord_2876090, baseEnd_2876090] using wordTrace_append hprefix tailTrace_2876090
  have hstable : (prefixWord ++ tailWord_2876090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876090).length < 2 ^ (prefixWord ++ tailWord_2876090).sum := by decide
  have hdescent : baseEnd_2876090 < baseStart_2876090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876096 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_2876096 : Nat := 118140960795 + 2876096 * 2 ^ 59
def prefixEnd_2876096 : Nat := 4983230072969 + 3 ^ 40 * 2876096 * 2
def baseEnd_2876096 : Nat := 492273218824561498291027

theorem tailTrace_2876096 : CollatzResearch.WordTrace tailWord_2876096 prefixEnd_2876096 492273218824561498291027 := by
  unfold tailWord_2876096
  simp only [CollatzResearch.WordTrace]
  refine ⟨52449919494201432467816071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69933225992268576623754761 52449919494201432467816071)
  ·
    refine ⟨78674879241302148701724107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52449919494201432467816071 78674879241302148701724107)
    ·
      refine ⟨118012318861953223052586161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78674879241302148701724107 118012318861953223052586161)
      ·
        refine ⟨88509239146464917289439621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118012318861953223052586161 88509239146464917289439621)
        ·
          refine ⟨16595482339962171991769929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88509239146464917289439621 16595482339962171991769929)
          ·
            refine ⟨12446611754971628993827447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16595482339962171991769929 12446611754971628993827447)
            ·
              refine ⟨18669917632457443490741171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446611754971628993827447 18669917632457443490741171)
              ·
                refine ⟨28004876448686165236111757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18669917632457443490741171 28004876448686165236111757)
                ·
                  refine ⟨10501828668257311963541909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28004876448686165236111757 10501828668257311963541909)
                  ·
                    refine ⟨492273218824561498291027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10501828668257311963541909 492273218824561498291027)
                    ·
                      rfl

theorem cell23_2876096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_2876096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876096 prefixEnd_2876096 := by exact prefixLift 2876096
  have htrace : WordTrace (prefixWord ++ tailWord_2876096) baseStart_2876096 baseEnd_2876096 := by
    simpa [prefixWord, tailWord_2876096, baseEnd_2876096] using wordTrace_append hprefix tailTrace_2876096
  have hstable : (prefixWord ++ tailWord_2876096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876096).length < 2 ^ (prefixWord ++ tailWord_2876096).sum := by decide
  have hdescent : baseEnd_2876096 < baseStart_2876096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876114 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_2876114 : Nat := 118140960795 + 2876114 * 2 ^ 59
def prefixEnd_2876114 : Nat := 4983230072969 + 3 ^ 40 * 2876114 * 2
def baseEnd_2876114 : Nat := 1476828899125465424447999

theorem tailTrace_2876114 : CollatzResearch.WordTrace tailWord_2876114 prefixEnd_2876114 1476828899125465424447999 := by
  unfold tailWord_2876114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225123875584413502446849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69933663668225102673191597 26225123875584413502446849)
  ·
    refine ⟨19668842906688310126835137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26225123875584413502446849 19668842906688310126835137)
    ·
      refine ⟨14751632180016232595126353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19668842906688310126835137 14751632180016232595126353)
      ·
        refine ⟨11063724135012174446344765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14751632180016232595126353 11063724135012174446344765)
        ·
          refine ⟨4148896550629565417379287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11063724135012174446344765 4148896550629565417379287)
          ·
            refine ⟨6223344825944348126068931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148896550629565417379287 6223344825944348126068931)
            ·
              refine ⟨9335017238916522189103397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223344825944348126068931 9335017238916522189103397)
              ·
                refine ⟨1750315732296847910456887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9335017238916522189103397 1750315732296847910456887)
                ·
                  refine ⟨2625473598445271865685331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750315732296847910456887 2625473598445271865685331)
                  ·
                    refine ⟨3938210397667907798527997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625473598445271865685331 3938210397667907798527997)
                    ·
                      refine ⟨1476828899125465424447999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938210397667907798527997 1476828899125465424447999)
                      ·
                        rfl

theorem cell23_2876114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_2876114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876114 prefixEnd_2876114 := by exact prefixLift 2876114
  have htrace : WordTrace (prefixWord ++ tailWord_2876114) baseStart_2876114 baseEnd_2876114 := by
    simpa [prefixWord, tailWord_2876114, baseEnd_2876114] using wordTrace_append hprefix tailTrace_2876114
  have hstable : (prefixWord ++ tailWord_2876114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876114).length < 2 ^ (prefixWord ++ tailWord_2876114).sum := by decide
  have hdescent : baseEnd_2876114 < baseStart_2876114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876133 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2876133 : Nat := 118140960795 + 2876133 * 2 ^ 59
def prefixEnd_2876133 : Nat := 4983230072969 + 3 ^ 40 * 2876133 * 2
def baseEnd_2876133 : Nat := 1476838655257900850110411

theorem tailTrace_2876133 : CollatzResearch.WordTrace tailWord_2876133 prefixEnd_2876133 1476838655257900850110411 := by
  unfold tailWord_2876133
  simp only [CollatzResearch.WordTrace]
  refine ⟨104901188489268820254729053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69934125659512546836486035 104901188489268820254729053)
  ·
    refine ⟨39337945683475807595523395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104901188489268820254729053 39337945683475807595523395)
    ·
      refine ⟨59006918525213711393285093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39337945683475807595523395 59006918525213711393285093)
      ·
        refine ⟨11063797223477570886240955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59006918525213711393285093 11063797223477570886240955)
        ·
          refine ⟨16595695835216356329361433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11063797223477570886240955 16595695835216356329361433)
          ·
            refine ⟨12446771876412267247021075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16595695835216356329361433 12446771876412267247021075)
            ·
              refine ⟨18670157814618400870531613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446771876412267247021075 18670157814618400870531613)
              ·
                refine ⟨7001309180481900326449355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18670157814618400870531613 7001309180481900326449355)
                ·
                  refine ⟨10501963770722850489674033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7001309180481900326449355 10501963770722850489674033)
                  ·
                    refine ⟨7876472828042137867255525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10501963770722850489674033 7876472828042137867255525)
                    ·
                      refine ⟨1476838655257900850110411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7876472828042137867255525 1476838655257900850110411)
                      ·
                        rfl

theorem cell23_2876133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2876133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876133 prefixEnd_2876133 := by exact prefixLift 2876133
  have htrace : WordTrace (prefixWord ++ tailWord_2876133) baseStart_2876133 baseEnd_2876133 := by
    simpa [prefixWord, tailWord_2876133, baseEnd_2876133] using wordTrace_append hprefix tailTrace_2876133
  have hstable : (prefixWord ++ tailWord_2876133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876133).length < 2 ^ (prefixWord ++ tailWord_2876133).sum := by decide
  have hdescent : baseEnd_2876133 < baseStart_2876133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876143 : List Nat := [1, 1, 2, 1, 5, 3, 3, 7]
def baseStart_2876143 : Nat := 118140960795 + 2876143 * 2 ^ 59
def prefixEnd_2876143 : Nat := 4983230072969 + 3 ^ 40 * 2876143 * 2
def baseEnd_2876143 : Nat := 54697918150535030036495

theorem tailTrace_2876143 : CollatzResearch.WordTrace tailWord_2876143 prefixEnd_2876143 54697918150535030036495 := by
  unfold tailWord_2876143
  simp only [CollatzResearch.WordTrace]
  refine ⟨104901553219232591962593083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69934368812821727975062055 104901553219232591962593083)
  ·
    refine ⟨157352329828848887943889625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104901553219232591962593083 157352329828848887943889625)
    ·
      refine ⟨118014247371636665957917219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157352329828848887943889625 118014247371636665957917219)
      ·
        refine ⟨177021371057454998936875829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118014247371636665957917219 177021371057454998936875829)
        ·
          refine ⟨16595753536636406150332109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177021371057454998936875829 16595753536636406150332109)
          ·
            refine ⟨6223407576238652306374541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16595753536636406150332109 6223407576238652306374541)
            ·
              refine ⟨2333777841089494614890453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6223407576238652306374541 2333777841089494614890453)
              ·
                refine ⟨54697918150535030036495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2333777841089494614890453 54697918150535030036495)
                ·
                  rfl

theorem cell23_2876143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 7].length) (baseStart_2876143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876143 prefixEnd_2876143 := by exact prefixLift 2876143
  have htrace : WordTrace (prefixWord ++ tailWord_2876143) baseStart_2876143 baseEnd_2876143 := by
    simpa [prefixWord, tailWord_2876143, baseEnd_2876143] using wordTrace_append hprefix tailTrace_2876143
  have hstable : (prefixWord ++ tailWord_2876143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876143).length < 2 ^ (prefixWord ++ tailWord_2876143).sum := by decide
  have hdescent : baseEnd_2876143 < baseStart_2876143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876148 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2876148 : Nat := 118140960795 + 2876148 * 2 ^ 59
def prefixEnd_2876148 : Nat := 4983230072969 + 3 ^ 40 * 2876148 * 2
def baseEnd_2876148 : Nat := 1476846357467718291422843

theorem tailTrace_2876148 : CollatzResearch.WordTrace tailWord_2876148 prefixEnd_2876148 1476846357467718291422843 := by
  unfold tailWord_2876148
  simp only [CollatzResearch.WordTrace]
  refine ⟨52450867792107238908262549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69934490389476318544350065 52450867792107238908262549)
  ·
    refine ⟨2458634427755026823824807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52450867792107238908262549 2458634427755026823824807)
    ·
      refine ⟨3687951641632540235737211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458634427755026823824807 3687951641632540235737211)
      ·
        refine ⟨5531927462448810353605817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3687951641632540235737211 5531927462448810353605817)
        ·
          refine ⟨4148945596836607765204363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5531927462448810353605817 4148945596836607765204363)
          ·
            refine ⟨6223418395254911647806545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148945596836607765204363 6223418395254911647806545)
            ·
              refine ⟨4667563796441183735854909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6223418395254911647806545 4667563796441183735854909)
              ·
                refine ⟨1750336423665443900945591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4667563796441183735854909 1750336423665443900945591)
                ·
                  refine ⟨2625504635498165851418387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750336423665443900945591 2625504635498165851418387)
                  ·
                    refine ⟨3938256953247248777127581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625504635498165851418387 3938256953247248777127581)
                    ·
                      refine ⟨1476846357467718291422843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938256953247248777127581 1476846357467718291422843)
                      ·
                        rfl

theorem cell23_2876148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2876148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876148 prefixEnd_2876148 := by exact prefixLift 2876148
  have htrace : WordTrace (prefixWord ++ tailWord_2876148) baseStart_2876148 baseEnd_2876148 := by
    simpa [prefixWord, tailWord_2876148, baseEnd_2876148] using wordTrace_append hprefix tailTrace_2876148
  have hstable : (prefixWord ++ tailWord_2876148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876148).length < 2 ^ (prefixWord ++ tailWord_2876148).sum := by decide
  have hdescent : baseEnd_2876148 < baseStart_2876148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876170 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2876170 : Nat := 118140960795 + 2876170 * 2 ^ 59
def prefixEnd_2876170 : Nat := 4983230072969 + 3 ^ 40 * 2876170 * 2
def baseEnd_2876170 : Nat := 1476857654042117205347741

theorem tailTrace_2876170 : CollatzResearch.WordTrace tailWord_2876170 prefixEnd_2876170 1476857654042117205347741 := by
  unfold tailWord_2876170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225634497533693893456491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69935025326756517049217309 26225634497533693893456491)
  ·
    refine ⟨39338451746300540840184737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26225634497533693893456491 39338451746300540840184737)
    ·
      refine ⟨29503838809725405630138553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39338451746300540840184737 29503838809725405630138553)
      ·
        refine ⟨22127879107294054222603915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29503838809725405630138553 22127879107294054222603915)
        ·
          refine ⟨33191818660941081333905873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22127879107294054222603915 33191818660941081333905873)
          ·
            refine ⟨24893863995705811000429405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33191818660941081333905873 24893863995705811000429405)
            ·
              refine ⟨9335198998389679125161027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24893863995705811000429405 9335198998389679125161027)
              ·
                refine ⟨14002798497584518687741541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9335198998389679125161027 14002798497584518687741541)
                ·
                  refine ⟨2625524718297097253951539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14002798497584518687741541 2625524718297097253951539)
                  ·
                    refine ⟨3938287077445645880927309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625524718297097253951539 3938287077445645880927309)
                    ·
                      refine ⟨1476857654042117205347741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938287077445645880927309 1476857654042117205347741)
                      ·
                        rfl

theorem cell23_2876170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2876170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876170 prefixEnd_2876170 := by exact prefixLift 2876170
  have htrace : WordTrace (prefixWord ++ tailWord_2876170) baseStart_2876170 baseEnd_2876170 := by
    simpa [prefixWord, tailWord_2876170, baseEnd_2876170] using wordTrace_append hprefix tailTrace_2876170
  have hstable : (prefixWord ++ tailWord_2876170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876170).length < 2 ^ (prefixWord ++ tailWord_2876170).sum := by decide
  have hdescent : baseEnd_2876170 < baseStart_2876170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876197 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_2876197 : Nat := 118140960795 + 2876197 * 2 ^ 59
def prefixEnd_2876197 : Nat := 4983230072969 + 3 ^ 40 * 2876197 * 2
def baseEnd_2876197 : Nat := 1476871518019788599710117

theorem tailTrace_2876197 : CollatzResearch.WordTrace tailWord_2876197 prefixEnd_2876197 1476871518019788599710117 := by
  unfold tailWord_2876197
  simp only [CollatzResearch.WordTrace]
  refine ⟨104903522761036959185058845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69935681840691306123372563 104903522761036959185058845)
  ·
    refine ⟨39338821035388859694397067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104903522761036959185058845 39338821035388859694397067)
    ·
      refine ⟨59008231553083289541595601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39338821035388859694397067 59008231553083289541595601)
      ·
        refine ⟨44256173664812467156196701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59008231553083289541595601 44256173664812467156196701)
        ·
          refine ⟨16596065124304675183573763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44256173664812467156196701 16596065124304675183573763)
          ·
            refine ⟨24894097686457012775360645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16596065124304675183573763 24894097686457012775360645)
            ·
              refine ⟨4667643316210689895380121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24894097686457012775360645 4667643316210689895380121)
              ·
                refine ⟨3500732487158017421535091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667643316210689895380121 3500732487158017421535091)
                ·
                  refine ⟨5251098730737026132302637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500732487158017421535091 5251098730737026132302637)
                  ·
                    refine ⟨1969162024026384799613489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5251098730737026132302637 1969162024026384799613489)
                    ·
                      refine ⟨1476871518019788599710117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969162024026384799613489 1476871518019788599710117)
                      ·
                        rfl

theorem cell23_2876197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_2876197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876197 prefixEnd_2876197 := by exact prefixLift 2876197
  have htrace : WordTrace (prefixWord ++ tailWord_2876197) baseStart_2876197 baseEnd_2876197 := by
    simpa [prefixWord, tailWord_2876197, baseEnd_2876197] using wordTrace_append hprefix tailTrace_2876197
  have hstable : (prefixWord ++ tailWord_2876197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876197).length < 2 ^ (prefixWord ++ tailWord_2876197).sum := by decide
  have hdescent : baseEnd_2876197 < baseStart_2876197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876205 : List Nat := [1, 5, 3, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2876205 : Nat := 118140960795 + 2876205 * 2 ^ 59
def prefixEnd_2876205 : Nat := 4983230072969 + 3 ^ 40 * 2876205 * 2
def baseEnd_2876205 : Nat := 1476875625865024568410081

theorem tailTrace_2876205 : CollatzResearch.WordTrace tailWord_2876205 prefixEnd_2876205 1476875625865024568410081 := by
  unfold tailWord_2876205
  simp only [CollatzResearch.WordTrace]
  refine ⟨104903814545007976551350069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69935876363338651034233379 104903814545007976551350069)
  ·
    refine ⟨9834732613594497801689069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104903814545007976551350069 9834732613594497801689069)
    ·
      refine ⟨3688024730097936675633401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9834732613594497801689069 3688024730097936675633401)
      ·
        refine ⟨2766018547573452506725051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3688024730097936675633401 2766018547573452506725051)
        ·
          refine ⟨4149027821360178760087577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766018547573452506725051 4149027821360178760087577)
          ·
            refine ⟨3111770866020134070065683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149027821360178760087577 3111770866020134070065683)
            ·
              refine ⟨4667656299030201105098525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111770866020134070065683 4667656299030201105098525)
              ·
                refine ⟨1750371112136325414411947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4667656299030201105098525 1750371112136325414411947)
                ·
                  refine ⟨2625556668204488121617921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750371112136325414411947 2625556668204488121617921)
                  ·
                    refine ⟨1969167501153366091213441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2625556668204488121617921 1969167501153366091213441)
                    ·
                      refine ⟨1476875625865024568410081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969167501153366091213441 1476875625865024568410081)
                      ·
                        rfl

theorem cell23_2876205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2876205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876205 prefixEnd_2876205 := by exact prefixLift 2876205
  have htrace : WordTrace (prefixWord ++ tailWord_2876205) baseStart_2876205 baseEnd_2876205 := by
    simpa [prefixWord, tailWord_2876205, baseEnd_2876205] using wordTrace_append hprefix tailTrace_2876205
  have hstable : (prefixWord ++ tailWord_2876205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876205).length < 2 ^ (prefixWord ++ tailWord_2876205).sum := by decide
  have hdescent : baseEnd_2876205 < baseStart_2876205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876210 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_2876210 : Nat := 118140960795 + 2876210 * 2 ^ 59
def prefixEnd_2876210 : Nat := 4983230072969 + 3 ^ 40 * 2876210 * 2
def baseEnd_2876210 : Nat := 1476878193268297048847557

theorem tailTrace_2876210 : CollatzResearch.WordTrace tailWord_2876210 prefixEnd_2876210 1476878193268297048847557 := by
  unfold tailWord_2876210
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225999227497465601320521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69935997939993241603521389 26225999227497465601320521)
  ·
    refine ⟨19669499420623099200990391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26225999227497465601320521 19669499420623099200990391)
    ·
      refine ⟨29504249130934648801485587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19669499420623099200990391 29504249130934648801485587)
      ·
        refine ⟨44256373696401973202228381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29504249130934648801485587 44256373696401973202228381)
        ·
          refine ⟨16596140136150739950835643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44256373696401973202228381 16596140136150739950835643)
          ·
            refine ⟨24894210204226109926253465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16596140136150739950835643 24894210204226109926253465)
            ·
              refine ⟨18670657653169582444690099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24894210204226109926253465 18670657653169582444690099)
              ·
                refine ⟨28005986479754373667035149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18670657653169582444690099 28005986479754373667035149)
                ·
                  refine ⟨10502244929907890125138181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28005986479754373667035149 10502244929907890125138181)
                  ·
                    refine ⟨1969170924357729398463409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10502244929907890125138181 1969170924357729398463409)
                    ·
                      refine ⟨1476878193268297048847557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969170924357729398463409 1476878193268297048847557)
                      ·
                        rfl

theorem cell23_2876210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_2876210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876210 prefixEnd_2876210 := by exact prefixLift 2876210
  have htrace : WordTrace (prefixWord ++ tailWord_2876210) baseStart_2876210 baseEnd_2876210 := by
    simpa [prefixWord, tailWord_2876210, baseEnd_2876210] using wordTrace_append hprefix tailTrace_2876210
  have hstable : (prefixWord ++ tailWord_2876210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876210).length < 2 ^ (prefixWord ++ tailWord_2876210).sum := by decide
  have hdescent : baseEnd_2876210 < baseStart_2876210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876213 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2876213 : Nat := 118140960795 + 2876213 * 2 ^ 59
def prefixEnd_2876213 : Nat := 4983230072969 + 3 ^ 40 * 2876213 * 2
def baseEnd_2876213 : Nat := 1476879733710260537110043

theorem tailTrace_2876213 : CollatzResearch.WordTrace tailWord_2876213 prefixEnd_2876213 1476879733710260537110043 := by
  unfold tailWord_2876213
  simp only [CollatzResearch.WordTrace]
  refine ⟨104904106328978993917641293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69936070885985995945094195 104904106328978993917641293)
  ·
    refine ⟨39339039873367122719115485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104904106328978993917641293 39339039873367122719115485)
    ·
      refine ⟨14752139952512671019668307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39339039873367122719115485 14752139952512671019668307)
      ·
        refine ⟨22128209928769006529502461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14752139952512671019668307 22128209928769006529502461)
        ·
          refine ⟨8298078723288377448563423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22128209928769006529502461 8298078723288377448563423)
          ·
            refine ⟨12447118084932566172845135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298078723288377448563423 12447118084932566172845135)
            ·
              refine ⟨18670677127398849259267703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12447118084932566172845135 18670677127398849259267703)
              ·
                refine ⟨28006015691098273888901555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18670677127398849259267703 28006015691098273888901555)
                ·
                  refine ⟨42009023536647410833352333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28006015691098273888901555 42009023536647410833352333)
                  ·
                    refine ⟨15753383826242779062507125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42009023536647410833352333 15753383826242779062507125)
                    ·
                      refine ⟨1476879733710260537110043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15753383826242779062507125 1476879733710260537110043)
                      ·
                        rfl

theorem cell23_2876213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2876213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876213 prefixEnd_2876213 := by exact prefixLift 2876213
  have htrace : WordTrace (prefixWord ++ tailWord_2876213) baseStart_2876213 baseEnd_2876213 := by
    simpa [prefixWord, tailWord_2876213, baseEnd_2876213] using wordTrace_append hprefix tailTrace_2876213
  have hstable : (prefixWord ++ tailWord_2876213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876213).length < 2 ^ (prefixWord ++ tailWord_2876213).sum := by decide
  have hdescent : baseEnd_2876213 < baseStart_2876213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876227 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 2, 2, 2]
def baseStart_2876227 : Nat := 118140960795 + 2876227 * 2 ^ 59
def prefixEnd_2876227 : Nat := 4983230072969 + 3 ^ 40 * 2876227 * 2
def baseEnd_2876227 : Nat := 1476886922439423482334979

theorem tailTrace_2876227 : CollatzResearch.WordTrace tailWord_2876227 prefixEnd_2876227 1476886922439423482334979 := by
  unfold tailWord_2876227
  simp only [CollatzResearch.WordTrace]
  refine ⟨104904616950928274308650935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69936411300618849539100623 104904616950928274308650935)
  ·
    refine ⟨157356925426392411462976403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104904616950928274308650935 157356925426392411462976403)
    ·
      refine ⟨236035388139588617194464605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157356925426392411462976403 236035388139588617194464605)
      ·
        refine ⟨88513270552345731447924227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236035388139588617194464605 88513270552345731447924227)
        ·
          refine ⟨132769905828518597171886341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88513270552345731447924227 132769905828518597171886341)
          ·
            refine ⟨24894357342847236969728689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132769905828518597171886341 24894357342847236969728689)
            ·
              refine ⟨18670768007135427727296517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24894357342847236969728689 18670768007135427727296517)
              ·
                refine ⟨3500769001337892698868097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18670768007135427727296517 3500769001337892698868097)
                ·
                  refine ⟨2625576751003419524151073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3500769001337892698868097 2625576751003419524151073)
                  ·
                    refine ⟨1969182563252564643113305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2625576751003419524151073 1969182563252564643113305)
                    ·
                      refine ⟨1476886922439423482334979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969182563252564643113305 1476886922439423482334979)
                      ·
                        rfl

theorem cell23_2876227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_2876227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876227 prefixEnd_2876227 := by exact prefixLift 2876227
  have htrace : WordTrace (prefixWord ++ tailWord_2876227) baseStart_2876227 baseEnd_2876227 := by
    simpa [prefixWord, tailWord_2876227, baseEnd_2876227] using wordTrace_append hprefix tailTrace_2876227
  have hstable : (prefixWord ++ tailWord_2876227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876227).length < 2 ^ (prefixWord ++ tailWord_2876227).sum := by decide
  have hdescent : baseEnd_2876227 < baseStart_2876227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876233 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 7]
def baseStart_2876233 : Nat := 118140960795 + 2876233 * 2 ^ 59
def prefixEnd_2876233 : Nat := 4983230072969 + 3 ^ 40 * 2876233 * 2
def baseEnd_2876233 : Nat := 164098889258150050984439

theorem tailTrace_2876233 : CollatzResearch.WordTrace tailWord_2876233 prefixEnd_2876233 164098889258150050984439 := by
  unfold tailWord_2876233
  simp only [CollatzResearch.WordTrace]
  refine ⟨104904835788906537333369353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69936557192604358222246235 104904835788906537333369353)
  ·
    refine ⟨78678626841679903000027015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104904835788906537333369353 78678626841679903000027015)
    ·
      refine ⟨118017940262519854500040523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78678626841679903000027015 118017940262519854500040523)
      ·
        refine ⟨177026910393779781750060785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118017940262519854500040523 177026910393779781750060785)
        ·
          refine ⟨132770182795334836312545589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177026910393779781750060785 132770182795334836312545589)
          ·
            refine ⟨12447204637062640904301149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132770182795334836312545589 12447204637062640904301149)
            ·
              refine ⟨4667701738898490339112931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12447204637062640904301149 4667701738898490339112931)
              ·
                refine ⟨7001552608347735508669397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667701738898490339112931 7001552608347735508669397)
                ·
                  refine ⟨164098889258150050984439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7001552608347735508669397 164098889258150050984439)
                  ·
                    rfl

theorem cell23_2876233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_2876233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876233 prefixEnd_2876233 := by exact prefixLift 2876233
  have htrace : WordTrace (prefixWord ++ tailWord_2876233) baseStart_2876233 baseEnd_2876233 := by
    simpa [prefixWord, tailWord_2876233, baseEnd_2876233] using wordTrace_append hprefix tailTrace_2876233
  have hstable : (prefixWord ++ tailWord_2876233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876233).length < 2 ^ (prefixWord ++ tailWord_2876233).sum := by decide
  have hdescent : baseEnd_2876233 < baseStart_2876233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876243 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3]
def baseStart_2876243 : Nat := 118140960795 + 2876243 * 2 ^ 59
def prefixEnd_2876243 : Nat := 4983230072969 + 3 ^ 40 * 2876243 * 2
def baseEnd_2876243 : Nat := 1476895138129895419734905

theorem tailTrace_2876243 : CollatzResearch.WordTrace tailWord_2876243 prefixEnd_2876243 1476895138129895419734905 := by
  unfold tailWord_2876243
  simp only [CollatzResearch.WordTrace]
  refine ⟨104905200518870309041233383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69936800345913539360822255 104905200518870309041233383)
  ·
    refine ⟨157357800778305463561850075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104905200518870309041233383 157357800778305463561850075)
    ·
      refine ⟨236036701167458195342775113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157357800778305463561850075 236036701167458195342775113)
      ·
        refine ⟨177027525875593646507081335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236036701167458195342775113 177027525875593646507081335)
        ·
          refine ⟨265541288813390469760622003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177027525875593646507081335 265541288813390469760622003)
          ·
            refine ⟨398311933220085704640933005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265541288813390469760622003 398311933220085704640933005)
            ·
              refine ⟨149366974957532139240349877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398311933220085704640933005 149366974957532139240349877)
              ·
                refine ⟨14003153902268638053782801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149366974957532139240349877 14003153902268638053782801)
                ·
                  refine ⟨10502365426701478540337101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14003153902268638053782801 10502365426701478540337101)
                  ·
                    refine ⟨3938387035013054452626413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10502365426701478540337101 3938387035013054452626413)
                    ·
                      refine ⟨1476895138129895419734905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938387035013054452626413 1476895138129895419734905)
                      ·
                        rfl

theorem cell23_2876243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_2876243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876243 prefixEnd_2876243 := by exact prefixLift 2876243
  have htrace : WordTrace (prefixWord ++ tailWord_2876243) baseStart_2876243 baseEnd_2876243 := by
    simpa [prefixWord, tailWord_2876243, baseEnd_2876243] using wordTrace_append hprefix tailTrace_2876243
  have hstable : (prefixWord ++ tailWord_2876243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876243).length < 2 ^ (prefixWord ++ tailWord_2876243).sum := by decide
  have hdescent : baseEnd_2876243 < baseStart_2876243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876273 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2876273 : Nat := 118140960795 + 2876273 * 2 ^ 59
def prefixEnd_2876273 : Nat := 4983230072969 + 3 ^ 40 * 2876273 * 2
def baseEnd_2876273 : Nat := 1476910542549530302359767

theorem tailTrace_2876273 : CollatzResearch.WordTrace tailWord_2876273 prefixEnd_2876273 1476910542549530302359767 := by
  unfold tailWord_2876273
  simp only [CollatzResearch.WordTrace]
  refine ⟨104906294708761624164825473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69937529805841082776550315 104906294708761624164825473)
  ·
    refine ⟨78679721031571218123619105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104906294708761624164825473 78679721031571218123619105)
    ·
      refine ⟨59009790773678413592714329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78679721031571218123619105 59009790773678413592714329)
      ·
        refine ⟨44257343080258810194535747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59009790773678413592714329 44257343080258810194535747)
        ·
          refine ⟨66386014620388215291803621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44257343080258810194535747 66386014620388215291803621)
          ·
            refine ⟨12447377741322790367213179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66386014620388215291803621 12447377741322790367213179)
            ·
              refine ⟨18671066611984185550819769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12447377741322790367213179 18671066611984185550819769)
              ·
                refine ⟨14003299958988139163114827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18671066611984185550819769 14003299958988139163114827)
                ·
                  refine ⟨21004949938482208744672241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14003299958988139163114827 21004949938482208744672241)
                  ·
                    refine ⟨15753712453861656558504181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21004949938482208744672241 15753712453861656558504181)
                    ·
                      refine ⟨1476910542549530302359767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15753712453861656558504181 1476910542549530302359767)
                      ·
                        rfl

theorem cell23_2876273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2876273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876273 prefixEnd_2876273 := by exact prefixLift 2876273
  have htrace : WordTrace (prefixWord ++ tailWord_2876273) baseStart_2876273 baseEnd_2876273 := by
    simpa [prefixWord, tailWord_2876273, baseEnd_2876273] using wordTrace_append hprefix tailTrace_2876273
  have hstable : (prefixWord ++ tailWord_2876273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876273).length < 2 ^ (prefixWord ++ tailWord_2876273).sum := by decide
  have hdescent : baseEnd_2876273 < baseStart_2876273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876300 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_2876300 : Nat := 118140960795 + 2876300 * 2 ^ 59
def prefixEnd_2876300 : Nat := 4983230072969 + 3 ^ 40 * 2876300 * 2
def baseEnd_2876300 : Nat := 1476924406527201696722143

theorem tailTrace_2876300 : CollatzResearch.WordTrace tailWord_2876300 prefixEnd_2876300 1476924406527201696722143 := by
  unfold tailWord_2876300
  simp only [CollatzResearch.WordTrace]
  refine ⟨52453639739831903888029177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69938186319775871850705569 52453639739831903888029177)
  ·
    refine ⟨39340229804873927916021883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52453639739831903888029177 39340229804873927916021883)
    ·
      refine ⟨59010344707310891874032825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39340229804873927916021883 59010344707310891874032825)
      ·
        refine ⟨44257758530483168905524619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59010344707310891874032825 44257758530483168905524619)
        ·
          refine ⟨66386637795724753358286929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44257758530483168905524619 66386637795724753358286929)
          ·
            refine ⟨49789978346793565018715197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66386637795724753358286929 49789978346793565018715197)
            ·
              refine ⟨18671241880047586882018199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49789978346793565018715197 18671241880047586882018199)
              ·
                refine ⟨28006862820071380323027299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18671241880047586882018199 28006862820071380323027299)
                ·
                  refine ⟨42010294230107070484540949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28006862820071380323027299 42010294230107070484540949)
                  ·
                    refine ⟨1969232542036268928962857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42010294230107070484540949 1969232542036268928962857)
                    ·
                      refine ⟨1476924406527201696722143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969232542036268928962857 1476924406527201696722143)
                      ·
                        rfl

theorem cell23_2876300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_2876300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876300 prefixEnd_2876300 := by exact prefixLift 2876300
  have htrace : WordTrace (prefixWord ++ tailWord_2876300) baseStart_2876300 baseEnd_2876300 := by
    simpa [prefixWord, tailWord_2876300, baseEnd_2876300] using wordTrace_append hprefix tailTrace_2876300
  have hstable : (prefixWord ++ tailWord_2876300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876300).length < 2 ^ (prefixWord ++ tailWord_2876300).sum := by decide
  have hdescent : baseEnd_2876300 < baseStart_2876300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876314 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_2876314 : Nat := 118140960795 + 2876314 * 2 ^ 59
def prefixEnd_2876314 : Nat := 4983230072969 + 3 ^ 40 * 2876314 * 2
def baseEnd_2876314 : Nat := 492310531752121547315693

theorem tailTrace_2876314 : CollatzResearch.WordTrace tailWord_2876314 prefixEnd_2876314 492310531752121547315693 := by
  unfold tailWord_2876314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26226947525403272041766999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69938526734408725444711997 26226947525403272041766999)
  ·
    refine ⟨39340421288104908062650499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26226947525403272041766999 39340421288104908062650499)
    ·
      refine ⟨59010631932157362093975749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39340421288104908062650499 59010631932157362093975749)
      ·
        refine ⟨11064493487279505392620453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59010631932157362093975749 11064493487279505392620453)
        ·
          refine ⟨2074592528864907261116335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11064493487279505392620453 2074592528864907261116335)
          ·
            refine ⟨3111888793297360891674503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074592528864907261116335 3111888793297360891674503)
            ·
              refine ⟨4667833189946041337511755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111888793297360891674503 4667833189946041337511755)
              ·
                refine ⟨7001749784919062006267633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667833189946041337511755 7001749784919062006267633)
                ·
                  refine ⟨5251312338689296504700725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7001749784919062006267633 5251312338689296504700725)
                  ·
                    refine ⟨492310531752121547315693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5251312338689296504700725 492310531752121547315693)
                    ·
                      rfl

theorem cell23_2876314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_2876314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876314 prefixEnd_2876314 := by exact prefixLift 2876314
  have htrace : WordTrace (prefixWord ++ tailWord_2876314) baseStart_2876314 baseEnd_2876314 := by
    simpa [prefixWord, tailWord_2876314, baseEnd_2876314] using wordTrace_append hprefix tailTrace_2876314
  have hstable : (prefixWord ++ tailWord_2876314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876314).length < 2 ^ (prefixWord ++ tailWord_2876314).sum := by decide
  have hdescent : baseEnd_2876314 < baseStart_2876314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876343 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2876343 : Nat := 118140960795 + 2876343 * 2 ^ 59
def prefixEnd_2876343 : Nat := 4983230072969 + 3 ^ 40 * 2876343 * 2
def baseEnd_2876343 : Nat := 1476946486195345028484445

theorem tailTrace_2876343 : CollatzResearch.WordTrace tailWord_2876343 prefixEnd_2876343 1476946486195345028484445 := by
  unfold tailWord_2876343
  simp only [CollatzResearch.WordTrace]
  refine ⟨104908847818508026119873683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69939231879005350746582455 104908847818508026119873683)
  ·
    refine ⟨157363271727762039179810525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104908847818508026119873683 157363271727762039179810525)
    ·
      refine ⟨59011226897910764692428947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157363271727762039179810525 59011226897910764692428947)
      ·
        refine ⟨88516840346866147038643421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59011226897910764692428947 88516840346866147038643421)
        ·
          refine ⟨33193815130074805139491283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88516840346866147038643421 33193815130074805139491283)
          ·
            refine ⟨49790722695112207709236925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33193815130074805139491283 49790722695112207709236925)
            ·
              refine ⟨18671521010667077890963847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49790722695112207709236925 18671521010667077890963847)
              ·
                refine ⟨28007281516000616836445771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18671521010667077890963847 28007281516000616836445771)
                ·
                  refine ⟨42010922274000925254668657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28007281516000616836445771 42010922274000925254668657)
                  ·
                    refine ⟨31508191705500693941001493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42010922274000925254668657 31508191705500693941001493)
                    ·
                      refine ⟨1476946486195345028484445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31508191705500693941001493 1476946486195345028484445)
                      ·
                        rfl

theorem cell23_2876343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2876343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876343 prefixEnd_2876343 := by exact prefixLift 2876343
  have htrace : WordTrace (prefixWord ++ tailWord_2876343) baseStart_2876343 baseEnd_2876343 := by
    simpa [prefixWord, tailWord_2876343, baseEnd_2876343] using wordTrace_append hprefix tailTrace_2876343
  have hstable : (prefixWord ++ tailWord_2876343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876343).length < 2 ^ (prefixWord ++ tailWord_2876343).sum := by decide
  have hdescent : baseEnd_2876343 < baseStart_2876343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876367 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 3]
def baseStart_2876367 : Nat := 118140960795 + 2876367 * 2 ^ 59
def prefixEnd_2876367 : Nat := 4983230072969 + 3 ^ 40 * 2876367 * 2
def baseEnd_2876367 : Nat := 1476958809731052934584335

theorem tailTrace_2876367 : CollatzResearch.WordTrace tailWord_2876367 prefixEnd_2876367 1476958809731052934584335 := by
  unfold tailWord_2876367
  simp only [CollatzResearch.WordTrace]
  refine ⟨104909723170421078218747355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69939815446947385479164903 104909723170421078218747355)
  ·
    refine ⟨157364584755631617328121033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104909723170421078218747355 157364584755631617328121033)
    ·
      refine ⟨118023438566723712996090775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157364584755631617328121033 118023438566723712996090775)
      ·
        refine ⟨177035157850085569494136163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118023438566723712996090775 177035157850085569494136163)
        ·
          refine ⟨265552736775128354241204245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177035157850085569494136163 265552736775128354241204245)
          ·
            refine ⟨12447784536334141605056449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265552736775128354241204245 12447784536334141605056449)
            ·
              refine ⟨9335838402250606203792337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12447784536334141605056449 9335838402250606203792337)
              ·
                refine ⟨7001878801687954652844253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9335838402250606203792337 7001878801687954652844253)
                ·
                  refine ⟨2625704550632982994816595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7001878801687954652844253 2625704550632982994816595)
                  ·
                    refine ⟨3938556825949474492224893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625704550632982994816595 3938556825949474492224893)
                    ·
                      refine ⟨1476958809731052934584335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938556825949474492224893 1476958809731052934584335)
                      ·
                        rfl

theorem cell23_2876367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_2876367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876367 prefixEnd_2876367 := by exact prefixLift 2876367
  have htrace : WordTrace (prefixWord ++ tailWord_2876367) baseStart_2876367 baseEnd_2876367 := by
    simpa [prefixWord, tailWord_2876367, baseEnd_2876367] using wordTrace_append hprefix tailTrace_2876367
  have hstable : (prefixWord ++ tailWord_2876367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876367).length < 2 ^ (prefixWord ++ tailWord_2876367).sum := by decide
  have hdescent : baseEnd_2876367 < baseStart_2876367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876377 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 5, 2]
def baseStart_2876377 : Nat := 118140960795 + 2876377 * 2 ^ 59
def prefixEnd_2876377 : Nat := 4983230072969 + 3 ^ 40 * 2876377 * 2
def baseEnd_2876377 : Nat := 1476963944537597895459289

theorem tailTrace_2876377 : CollatzResearch.WordTrace tailWord_2876377 prefixEnd_2876377 1476963944537597895459289 := by
  unfold tailWord_2876377
  simp only [CollatzResearch.WordTrace]
  refine ⟨104910087900384849926611385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69940058600256566617740923 104910087900384849926611385)
  ·
    refine ⟨78682565925288637444958539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104910087900384849926611385 78682565925288637444958539)
    ·
      refine ⟨118023848887932956167437809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78682565925288637444958539 118023848887932956167437809)
      ·
        refine ⟨88517886665949717125578357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118023848887932956167437809 88517886665949717125578357)
        ·
          refine ⟨8298551874932785980522971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88517886665949717125578357 8298551874932785980522971)
          ·
            refine ⟨12447827812399178970784457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298551874932785980522971 12447827812399178970784457)
            ·
              refine ⟨9335870859299384228088343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12447827812399178970784457 9335870859299384228088343)
              ·
                refine ⟨14003806288949076342132515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9335870859299384228088343 14003806288949076342132515)
                ·
                  refine ⟨21005709433423614513198773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14003806288949076342132515 21005709433423614513198773)
                  ·
                    refine ⟨1969285259383463860612385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21005709433423614513198773 1969285259383463860612385)
                    ·
                      refine ⟨1476963944537597895459289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969285259383463860612385 1476963944537597895459289)
                      ·
                        rfl

theorem cell23_2876377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_2876377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876377 prefixEnd_2876377 := by exact prefixLift 2876377
  have htrace : WordTrace (prefixWord ++ tailWord_2876377) baseStart_2876377 baseEnd_2876377 := by
    simpa [prefixWord, tailWord_2876377, baseEnd_2876377] using wordTrace_append hprefix tailTrace_2876377
  have hstable : (prefixWord ++ tailWord_2876377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876377).length < 2 ^ (prefixWord ++ tailWord_2876377).sum := by decide
  have hdescent : baseEnd_2876377 < baseStart_2876377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876394 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_2876394 : Nat := 118140960795 + 2876394 * 2 ^ 59
def prefixEnd_2876394 : Nat := 4983230072969 + 3 ^ 40 * 2876394 * 2
def baseEnd_2876394 : Nat := 1476972673708724328946711

theorem tailTrace_2876394 : CollatzResearch.WordTrace tailWord_2876394 prefixEnd_2876394 1476972673708724328946711 := by
  unfold tailWord_2876394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26227676985330815457495059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69940471960882174553320157 26227676985330815457495059)
  ·
    refine ⟨39341515477996223186242589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26227676985330815457495059 39341515477996223186242589)
    ·
      refine ⟨14753068304248583694840971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39341515477996223186242589 14753068304248583694840971)
      ·
        refine ⟨22129602456372875542261457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14753068304248583694840971 22129602456372875542261457)
        ·
          refine ⟨16597201842279656656696093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22129602456372875542261457 16597201842279656656696093)
          ·
            refine ⟨6223950690854871246261035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16597201842279656656696093 6223950690854871246261035)
            ·
              refine ⟨9335926036282306869391553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223950690854871246261035 9335926036282306869391553)
              ·
                refine ⟨7001944527211730152043665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9335926036282306869391553 7001944527211730152043665)
                ·
                  refine ⟨5251458395408797614032749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7001944527211730152043665 5251458395408797614032749)
                  ·
                    refine ⟨1969296898278299105262281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5251458395408797614032749 1969296898278299105262281)
                    ·
                      refine ⟨1476972673708724328946711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969296898278299105262281 1476972673708724328946711)
                      ·
                        rfl

theorem cell23_2876394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_2876394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876394 prefixEnd_2876394 := by exact prefixLift 2876394
  have htrace : WordTrace (prefixWord ++ tailWord_2876394) baseStart_2876394 baseEnd_2876394 := by
    simpa [prefixWord, tailWord_2876394, baseEnd_2876394] using wordTrace_append hprefix tailTrace_2876394
  have hstable : (prefixWord ++ tailWord_2876394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876394).length < 2 ^ (prefixWord ++ tailWord_2876394).sum := by decide
  have hdescent : baseEnd_2876394 < baseStart_2876394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876424 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2876424 : Nat := 118140960795 + 2876424 * 2 ^ 59
def prefixEnd_2876424 : Nat := 4983230072969 + 3 ^ 40 * 2876424 * 2
def baseEnd_2876424 : Nat := 1476988078128359211571573

theorem tailTrace_2876424 : CollatzResearch.WordTrace tailWord_2876424 prefixEnd_2876424 1476988078128359211571573 := by
  unfold tailWord_2876424
  simp only [CollatzResearch.WordTrace]
  refine ⟨52455901065607288476786163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69941201420809717969048217 52455901065607288476786163)
  ·
    refine ⟨78683851598410932715179245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52455901065607288476786163 78683851598410932715179245)
    ·
      refine ⟨29506444349404099768192217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78683851598410932715179245 29506444349404099768192217)
      ·
        refine ⟨22129833262053074826144163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29506444349404099768192217 22129833262053074826144163)
        ·
          refine ⟨33194749893079612239216245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22129833262053074826144163 33194749893079612239216245)
          ·
            refine ⟨3112007802476213647426523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33194749893079612239216245 3112007802476213647426523)
            ·
              refine ⟨4668011703714320471139785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112007802476213647426523 4668011703714320471139785)
              ·
                refine ⟨3501008777785740353354839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4668011703714320471139785 3501008777785740353354839)
                ·
                  refine ⟨5251513166678610530032259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501008777785740353354839 5251513166678610530032259)
                  ·
                    refine ⟨7877269750017915795048389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5251513166678610530032259 7877269750017915795048389)
                    ·
                      refine ⟨1476988078128359211571573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7877269750017915795048389 1476988078128359211571573)
                      ·
                        rfl

theorem cell23_2876424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2876424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876424 prefixEnd_2876424 := by exact prefixLift 2876424
  have htrace : WordTrace (prefixWord ++ tailWord_2876424) baseStart_2876424 baseEnd_2876424 := by
    simpa [prefixWord, tailWord_2876424, baseEnd_2876424] using wordTrace_append hprefix tailTrace_2876424
  have hstable : (prefixWord ++ tailWord_2876424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876424).length < 2 ^ (prefixWord ++ tailWord_2876424).sum := by decide
  have hdescent : baseEnd_2876424 < baseStart_2876424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876427 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3]
def baseStart_2876427 : Nat := 118140960795 + 2876427 * 2 ^ 59
def prefixEnd_2876427 : Nat := 4983230072969 + 3 ^ 40 * 2876427 * 2
def baseEnd_2876427 : Nat := 1476989618570322699834059

theorem tailTrace_2876427 : CollatzResearch.WordTrace tailWord_2876427 prefixEnd_2876427 1476989618570322699834059 := by
  unfold tailWord_2876427
  simp only [CollatzResearch.WordTrace]
  refine ⟨104911911550203708465931535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69941274366802472310621023 104911911550203708465931535)
  ·
    refine ⟨157367867325305562698897303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104911911550203708465931535 157367867325305562698897303)
    ·
      refine ⟨236051800987958344048345955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157367867325305562698897303 236051800987958344048345955)
      ·
        refine ⟨354077701481937516072518933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236051800987958344048345955 354077701481937516072518933)
        ·
          refine ⟨16597392256965821065899325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 354077701481937516072518933 16597392256965821065899325)
          ·
            refine ⟨6224022096362182899712247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16597392256965821065899325 6224022096362182899712247)
            ·
              refine ⟨9336033144543274349568371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224022096362182899712247 9336033144543274349568371)
              ·
                refine ⟨14004049716814911524352557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9336033144543274349568371 14004049716814911524352557)
                ·
                  refine ⟨5251518643805591821632209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14004049716814911524352557 5251518643805591821632209)
                  ·
                    refine ⟨3938638982854193866224157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5251518643805591821632209 3938638982854193866224157)
                    ·
                      refine ⟨1476989618570322699834059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938638982854193866224157 1476989618570322699834059)
                      ·
                        rfl

theorem cell23_2876427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 3].length) (baseStart_2876427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876427 prefixEnd_2876427 := by exact prefixLift 2876427
  have htrace : WordTrace (prefixWord ++ tailWord_2876427) baseStart_2876427 baseEnd_2876427 := by
    simpa [prefixWord, tailWord_2876427, baseEnd_2876427] using wordTrace_append hprefix tailTrace_2876427
  have hstable : (prefixWord ++ tailWord_2876427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876427).length < 2 ^ (prefixWord ++ tailWord_2876427).sum := by decide
  have hdescent : baseEnd_2876427 < baseStart_2876427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876430 : List Nat := [4, 1, 1, 2, 2, 2, 2, 9]
def baseStart_2876430 : Nat := 118140960795 + 2876430 * 2 ^ 59
def prefixEnd_2876430 : Nat := 4983230072969 + 3 ^ 40 * 2876430 * 2
def baseEnd_2876430 : Nat := 54703376259714303262835

theorem tailTrace_2876430 : CollatzResearch.WordTrace tailWord_2876430 prefixEnd_2876430 54703376259714303262835 := by
  unfold tailWord_2876430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13114002621149104997286343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69941347312795226652193829 13114002621149104997286343)
  ·
    refine ⟨19671003931723657495929515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13114002621149104997286343 19671003931723657495929515)
    ·
      refine ⟨29506505897585486243894273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19671003931723657495929515 29506505897585486243894273)
      ·
        refine ⟨22129879423189114682920705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29506505897585486243894273 22129879423189114682920705)
        ·
          refine ⟨16597409567391836012190529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22129879423189114682920705 16597409567391836012190529)
          ·
            refine ⟨12448057175543877009142897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16597409567391836012190529 12448057175543877009142897)
            ·
              refine ⟨9336042881657907756857173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12448057175543877009142897 9336042881657907756857173)
              ·
                refine ⟨54703376259714303262835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9336042881657907756857173 54703376259714303262835)
                ·
                  rfl

theorem cell23_2876430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_2876430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876430 prefixEnd_2876430 := by exact prefixLift 2876430
  have htrace : WordTrace (prefixWord ++ tailWord_2876430) baseStart_2876430 baseEnd_2876430 := by
    simpa [prefixWord, tailWord_2876430, baseEnd_2876430] using wordTrace_append hprefix tailTrace_2876430
  have hstable : (prefixWord ++ tailWord_2876430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876430).length < 2 ^ (prefixWord ++ tailWord_2876430).sum := by decide
  have hdescent : baseEnd_2876430 < baseStart_2876430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876437 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2876437 : Nat := 118140960795 + 2876437 * 2 ^ 59
def prefixEnd_2876437 : Nat := 4983230072969 + 3 ^ 40 * 2876437 * 2
def baseEnd_2876437 : Nat := 1476994753376867660709013

theorem tailTrace_2876437 : CollatzResearch.WordTrace tailWord_2876437 prefixEnd_2876437 1476994753376867660709013 := by
  unfold tailWord_2876437
  simp only [CollatzResearch.WordTrace]
  refine ⟨104912276280167480173795565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69941517520111653449197043 104912276280167480173795565)
  ·
    refine ⟨39342103605062805065173337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104912276280167480173795565 39342103605062805065173337)
    ·
      refine ⟨29506577703797103798880003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39342103605062805065173337 29506577703797103798880003)
      ·
        refine ⟨44259866555695655698320005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29506577703797103798880003 44259866555695655698320005)
        ·
          refine ⟨8298724979192935443435001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44259866555695655698320005 8298724979192935443435001)
          ·
            refine ⟨6224043734394701582576251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8298724979192935443435001 6224043734394701582576251)
            ·
              refine ⟨9336065601592052373864377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224043734394701582576251 9336065601592052373864377)
              ·
                refine ⟨7002049201194039280398283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9336065601592052373864377 7002049201194039280398283)
                ·
                  refine ⟨10503073801791058920597425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002049201194039280398283 10503073801791058920597425)
                  ·
                    refine ⟨7877305351343294190448069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10503073801791058920597425 7877305351343294190448069)
                    ·
                      refine ⟨1476994753376867660709013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7877305351343294190448069 1476994753376867660709013)
                      ·
                        rfl

theorem cell23_2876437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2876437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876437 prefixEnd_2876437 := by exact prefixLift 2876437
  have htrace : WordTrace (prefixWord ++ tailWord_2876437) baseStart_2876437 baseEnd_2876437 := by
    simpa [prefixWord, tailWord_2876437, baseEnd_2876437] using wordTrace_append hprefix tailTrace_2876437
  have hstable : (prefixWord ++ tailWord_2876437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876437).length < 2 ^ (prefixWord ++ tailWord_2876437).sum := by decide
  have hdescent : baseEnd_2876437 < baseStart_2876437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876444 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2876444 : Nat := 118140960795 + 2876444 * 2 ^ 59
def prefixEnd_2876444 : Nat := 4983230072969 + 3 ^ 40 * 2876444 * 2
def baseEnd_2876444 : Nat := 1476998347741449133321481

theorem tailTrace_2876444 : CollatzResearch.WordTrace tailWord_2876444 prefixEnd_2876444 1476998347741449133321481 := by
  unfold tailWord_2876444
  simp only [CollatzResearch.WordTrace]
  refine ⟨52456265795571060184650193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69941687727428080246200257 52456265795571060184650193)
  ·
    refine ⟨39342199346678295138487645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52456265795571060184650193 39342199346678295138487645)
    ·
      refine ⟨14753324755004360676932867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39342199346678295138487645 14753324755004360676932867)
      ·
        refine ⟨22129987132506541015399301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14753324755004360676932867 22129987132506541015399301)
        ·
          refine ⟨4149372587344976440387369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22129987132506541015399301 4149372587344976440387369)
          ·
            refine ⟨3112029440508732330290527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149372587344976440387369 3112029440508732330290527)
            ·
              refine ⟨4668044160763098495435791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112029440508732330290527 4668044160763098495435791)
              ·
                refine ⟨7002066241144647743153687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668044160763098495435791 7002066241144647743153687)
                ·
                  refine ⟨10503099361716971614730531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002066241144647743153687 10503099361716971614730531)
                  ·
                    refine ⟨15754649042575457422095797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10503099361716971614730531 15754649042575457422095797)
                    ·
                      refine ⟨1476998347741449133321481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15754649042575457422095797 1476998347741449133321481)
                      ·
                        rfl

theorem cell23_2876444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2876444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876444 prefixEnd_2876444 := by exact prefixLift 2876444
  have htrace : WordTrace (prefixWord ++ tailWord_2876444) baseStart_2876444 baseEnd_2876444 := by
    simpa [prefixWord, tailWord_2876444, baseEnd_2876444] using wordTrace_append hprefix tailTrace_2876444
  have hstable : (prefixWord ++ tailWord_2876444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876444).length < 2 ^ (prefixWord ++ tailWord_2876444).sum := by decide
  have hdescent : baseEnd_2876444 < baseStart_2876444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876474 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_2876474 : Nat := 118140960795 + 2876474 * 2 ^ 59
def prefixEnd_2876474 : Nat := 4983230072969 + 3 ^ 40 * 2876474 * 2
def baseEnd_2876474 : Nat := 1477013752161084015946343

theorem tailTrace_2876474 : CollatzResearch.WordTrace tailWord_2876474 prefixEnd_2876474 1477013752161084015946343 := by
  unfold tailWord_2876474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26228406445258358873223119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69942417187355623661928317 26228406445258358873223119)
  ·
    refine ⟨39342609667887538309834679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26228406445258358873223119 39342609667887538309834679)
    ·
      refine ⟨59013914501831307464752019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39342609667887538309834679 59013914501831307464752019)
      ·
        refine ⟨88520871752746961197128029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59013914501831307464752019 88520871752746961197128029)
        ·
          refine ⟨33195326907280110448923011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88520871752746961197128029 33195326907280110448923011)
          ·
            refine ⟨49792990360920165673384517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33195326907280110448923011 49792990360920165673384517)
            ·
              refine ⟨9336185692672531063759597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49792990360920165673384517 9336185692672531063759597)
              ·
                refine ⟨3501069634752199148909849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9336185692672531063759597 3501069634752199148909849)
                ·
                  refine ⟨2625802226064149361682387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501069634752199148909849 2625802226064149361682387)
                  ·
                    refine ⟨3938703339096224042523581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2625802226064149361682387 3938703339096224042523581)
                    ·
                      refine ⟨1477013752161084015946343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938703339096224042523581 1477013752161084015946343)
                      ·
                        rfl

theorem cell23_2876474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_2876474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876474 prefixEnd_2876474 := by exact prefixLift 2876474
  have htrace : WordTrace (prefixWord ++ tailWord_2876474) baseStart_2876474 baseEnd_2876474 := by
    simpa [prefixWord, tailWord_2876474, baseEnd_2876474] using wordTrace_append hprefix tailTrace_2876474
  have hstable : (prefixWord ++ tailWord_2876474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876474).length < 2 ^ (prefixWord ++ tailWord_2876474).sum := by decide
  have hdescent : baseEnd_2876474 < baseStart_2876474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876480 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_2876480 : Nat := 118140960795 + 2876480 * 2 ^ 59
def prefixEnd_2876480 : Nat := 4983230072969 + 3 ^ 40 * 2876480 * 2
def baseEnd_2876480 : Nat := 1477016833045010992471315

theorem tailTrace_2876480 : CollatzResearch.WordTrace tailWord_2876480 prefixEnd_2876480 1477016833045010992471315 := by
  unfold tailWord_2876480
  simp only [CollatzResearch.WordTrace]
  refine ⟨52456922309505849258805447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69942563079341132345073929 52456922309505849258805447)
  ·
    refine ⟨78685383464258773888208171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52456922309505849258805447 78685383464258773888208171)
    ·
      refine ⟨118028075196388160832312257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78685383464258773888208171 118028075196388160832312257)
      ·
        refine ⟨88521056397291120624234193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118028075196388160832312257 88521056397291120624234193)
        ·
          refine ⟨66390792297968340468175645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88521056397291120624234193 66390792297968340468175645)
          ·
            refine ⟨24896547111738127675565867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66390792297968340468175645 24896547111738127675565867)
            ·
              refine ⟨37344820667607191513348801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24896547111738127675565867 37344820667607191513348801)
              ·
                refine ⟨28008615500705393635011601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37344820667607191513348801 28008615500705393635011601)
                ·
                  refine ⟨21006461625529045226258701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28008615500705393635011601 21006461625529045226258701)
                  ·
                    refine ⟨7877423109573391959847013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21006461625529045226258701 7877423109573391959847013)
                    ·
                      refine ⟨1477016833045010992471315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7877423109573391959847013 1477016833045010992471315)
                      ·
                        rfl

theorem cell23_2876480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_2876480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876480 prefixEnd_2876480 := by exact prefixLift 2876480
  have htrace : WordTrace (prefixWord ++ tailWord_2876480) baseStart_2876480 baseEnd_2876480 := by
    simpa [prefixWord, tailWord_2876480, baseEnd_2876480] using wordTrace_append hprefix tailTrace_2876480
  have hstable : (prefixWord ++ tailWord_2876480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876480).length < 2 ^ (prefixWord ++ tailWord_2876480).sum := by decide
  have hdescent : baseEnd_2876480 < baseStart_2876480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876567 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 4, 5]
def baseStart_2876567 : Nat := 118140960795 + 2876567 * 2 ^ 59
def prefixEnd_2876567 : Nat := 4983230072969 + 3 ^ 40 * 2876567 * 2
def baseEnd_2876567 : Nat := 492353835287317384027805

theorem tailTrace_2876567 : CollatzResearch.WordTrace tailWord_2876567 prefixEnd_2876567 492353835287317384027805 := by
  unfold tailWord_2876567
  simp only [CollatzResearch.WordTrace]
  refine ⟨104917017769696512376027955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69944678513131008250685303 104917017769696512376027955)
  ·
    refine ⟨157375526654544768564041933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104917017769696512376027955 157375526654544768564041933)
    ·
      refine ⟨59015822495454288211515725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157375526654544768564041933 59015822495454288211515725)
      ·
        refine ⟨22130933435795358079318397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59015822495454288211515725 22130933435795358079318397)
        ·
          refine ⟨8299100038423259279744399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22130933435795358079318397 8299100038423259279744399)
          ·
            refine ⟨12448650057634888919616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8299100038423259279744399 12448650057634888919616599)
            ·
              refine ⟨18672975086452333379424899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12448650057634888919616599 18672975086452333379424899)
              ·
                refine ⟨28009462629678500069137349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18672975086452333379424899 28009462629678500069137349)
                ·
                  refine ⟨5251774243064718762963253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28009462629678500069137349 5251774243064718762963253)
                  ·
                    refine ⟨492353835287317384027805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5251774243064718762963253 492353835287317384027805)
                    ·
                      rfl

theorem cell23_2876567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_2876567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876567 prefixEnd_2876567 := by exact prefixLift 2876567
  have htrace : WordTrace (prefixWord ++ tailWord_2876567) baseStart_2876567 baseEnd_2876567 := by
    simpa [prefixWord, tailWord_2876567, baseEnd_2876567] using wordTrace_append hprefix tailTrace_2876567
  have hstable : (prefixWord ++ tailWord_2876567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876567).length < 2 ^ (prefixWord ++ tailWord_2876567).sum := by decide
  have hdescent : baseEnd_2876567 < baseStart_2876567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876577 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2876577 : Nat := 118140960795 + 2876577 * 2 ^ 59
def prefixEnd_2876577 : Nat := 4983230072969 + 3 ^ 40 * 2876577 * 2
def baseEnd_2876577 : Nat := 1477066640668497112958369

theorem tailTrace_2876577 : CollatzResearch.WordTrace tailWord_2876577 prefixEnd_2876577 1477066640668497112958369 := by
  unfold tailWord_2876577
  simp only [CollatzResearch.WordTrace]
  refine ⟨104917382499660284083891985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69944921666440189389261323 104917382499660284083891985)
  ·
    refine ⟨78688036874745213062918989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104917382499660284083891985 78688036874745213062918989)
    ·
      refine ⟨29508013828029454898594621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78688036874745213062918989 29508013828029454898594621)
      ·
        refine ⟨11065505185511045586972983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29508013828029454898594621 11065505185511045586972983)
        ·
          refine ⟨16598257778266568380459475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11065505185511045586972983 16598257778266568380459475)
          ·
            refine ⟨24897386667399852570689213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16598257778266568380459475 24897386667399852570689213)
            ·
              refine ⟨9336520000274944714008455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24897386667399852570689213 9336520000274944714008455)
              ·
                refine ⟨14004780000412417071012683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9336520000274944714008455 14004780000412417071012683)
                ·
                  refine ⟨21007170000618625606519025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14004780000412417071012683 21007170000618625606519025)
                  ·
                    refine ⟨15755377500463969204889269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21007170000618625606519025 15755377500463969204889269)
                    ·
                      refine ⟨1477066640668497112958369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15755377500463969204889269 1477066640668497112958369)
                      ·
                        rfl

theorem cell23_2876577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2876577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876577 prefixEnd_2876577 := by exact prefixLift 2876577
  have htrace : WordTrace (prefixWord ++ tailWord_2876577) baseStart_2876577 baseEnd_2876577 := by
    simpa [prefixWord, tailWord_2876577, baseEnd_2876577] using wordTrace_append hprefix tailTrace_2876577
  have hstable : (prefixWord ++ tailWord_2876577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876577).length < 2 ^ (prefixWord ++ tailWord_2876577).sum := by decide
  have hdescent : baseEnd_2876577 < baseStart_2876577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876604 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2876604 : Nat := 118140960795 + 2876604 * 2 ^ 59
def prefixEnd_2876604 : Nat := 4983230072969 + 3 ^ 40 * 2876604 * 2
def baseEnd_2876604 : Nat := 1477080504646168507320745

theorem tailTrace_2876604 : CollatzResearch.WordTrace tailWord_2876604 prefixEnd_2876604 1477080504646168507320745 := by
  unfold tailWord_2876604
  simp only [CollatzResearch.WordTrace]
  refine ⟨52459183635281233847562433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69945578180374978463416577 52459183635281233847562433)
  ·
    refine ⟨39344387726460925385671825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52459183635281233847562433 39344387726460925385671825)
    ·
      refine ⟨29508290794845694039253869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39344387726460925385671825 29508290794845694039253869)
      ·
        refine ⟨11065609048067135264720201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29508290794845694039253869 11065609048067135264720201)
        ·
          refine ⟨8299206786050351448540151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11065609048067135264720201 8299206786050351448540151)
          ·
            refine ⟨12448810179075527172810227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8299206786050351448540151 12448810179075527172810227)
            ·
              refine ⟨18673215268613290759215341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12448810179075527172810227 18673215268613290759215341)
              ·
                refine ⟨7002455725729984034705753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18673215268613290759215341 7002455725729984034705753)
                ·
                  refine ⟨5251841794297488026029315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7002455725729984034705753 5251841794297488026029315)
                  ·
                    refine ⟨7877762691446232039043973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5251841794297488026029315 7877762691446232039043973)
                    ·
                      refine ⟨1477080504646168507320745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7877762691446232039043973 1477080504646168507320745)
                      ·
                        rfl

theorem cell23_2876604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2876604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876604 prefixEnd_2876604 := by exact prefixLift 2876604
  have htrace : WordTrace (prefixWord ++ tailWord_2876604) baseStart_2876604 baseEnd_2876604 := by
    simpa [prefixWord, tailWord_2876604, baseEnd_2876604] using wordTrace_append hprefix tailTrace_2876604
  have hstable : (prefixWord ++ tailWord_2876604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876604).length < 2 ^ (prefixWord ++ tailWord_2876604).sum := by decide
  have hdescent : baseEnd_2876604 < baseStart_2876604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876607 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_2876607 : Nat := 118140960795 + 2876607 * 2 ^ 59
def prefixEnd_2876607 : Nat := 4983230072969 + 3 ^ 40 * 2876607 * 2
def baseEnd_2876607 : Nat := 1477082045088131995583231

theorem tailTrace_2876607 : CollatzResearch.WordTrace tailWord_2876607 prefixEnd_2876607 1477082045088131995583231 := by
  unfold tailWord_2876607
  simp only [CollatzResearch.WordTrace]
  refine ⟨104918476689551599207484075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69945651126367732804989383 104918476689551599207484075)
  ·
    refine ⟨157377715034327398811226113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104918476689551599207484075 157377715034327398811226113)
    ·
      refine ⟨118033286275745549108419585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157377715034327398811226113 118033286275745549108419585)
      ·
        refine ⟨88524964706809161831314689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118033286275745549108419585 88524964706809161831314689)
        ·
          refine ⟨66393723530106871373486017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88524964706809161831314689 66393723530106871373486017)
          ·
            refine ⟨49795292647580153530114513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66393723530106871373486017 49795292647580153530114513)
            ·
              refine ⟨37346469485685115147585885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49795292647580153530114513 37346469485685115147585885)
              ·
                refine ⟨14004926057131918180344707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37346469485685115147585885 14004926057131918180344707)
                ·
                  refine ⟨21007389085697877270517061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14004926057131918180344707 21007389085697877270517061)
                  ·
                    refine ⟨3938885453568351988221949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21007389085697877270517061 3938885453568351988221949)
                    ·
                      refine ⟨1477082045088131995583231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938885453568351988221949 1477082045088131995583231)
                      ·
                        rfl

theorem cell23_2876607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_2876607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876607 prefixEnd_2876607 := by exact prefixLift 2876607
  have htrace : WordTrace (prefixWord ++ tailWord_2876607) baseStart_2876607 baseEnd_2876607 := by
    simpa [prefixWord, tailWord_2876607, baseEnd_2876607] using wordTrace_append hprefix tailTrace_2876607
  have hstable : (prefixWord ++ tailWord_2876607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876607).length < 2 ^ (prefixWord ++ tailWord_2876607).sum := by decide
  have hdescent : baseEnd_2876607 < baseStart_2876607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876658 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2876658 : Nat := 118140960795 + 2876658 * 2 ^ 59
def prefixEnd_2876658 : Nat := 4983230072969 + 3 ^ 40 * 2876658 * 2
def baseEnd_2876658 : Nat := 1477108232601511296045497

theorem tailTrace_2876658 : CollatzResearch.WordTrace tailWord_2876658 prefixEnd_2876658 1477108232601511296045497 := by
  unfold tailWord_2876658
  simp only [CollatzResearch.WordTrace]
  refine ⟨26230084203091708729397657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69946891208244556611727085 26230084203091708729397657)
  ·
    refine ⟨19672563152318781547048243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26230084203091708729397657 19672563152318781547048243)
    ·
      refine ⟨29508844728478172320572365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19672563152318781547048243 29508844728478172320572365)
      ·
        refine ⟨11065816773179314620214637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29508844728478172320572365 11065816773179314620214637)
        ·
          refine ⟨4149681289942242982580489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11065816773179314620214637 4149681289942242982580489)
          ·
            refine ⟨3112260967456682236935367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149681289942242982580489 3112260967456682236935367)
            ·
              refine ⟨4668391451185023355403051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112260967456682236935367 4668391451185023355403051)
              ·
                refine ⟨7002587176777535033104577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668391451185023355403051 7002587176777535033104577)
                ·
                  refine ⟨5251940382583151274828433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7002587176777535033104577 5251940382583151274828433)
                  ·
                    refine ⟨3938955286937363456121325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5251940382583151274828433 3938955286937363456121325)
                    ·
                      refine ⟨1477108232601511296045497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3938955286937363456121325 1477108232601511296045497)
                      ·
                        rfl

theorem cell23_2876658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2876658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876658 prefixEnd_2876658 := by exact prefixLift 2876658
  have htrace : WordTrace (prefixWord ++ tailWord_2876658) baseStart_2876658 baseEnd_2876658 := by
    simpa [prefixWord, tailWord_2876658, baseEnd_2876658] using wordTrace_append hprefix tailTrace_2876658
  have hstable : (prefixWord ++ tailWord_2876658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876658).length < 2 ^ (prefixWord ++ tailWord_2876658).sum := by decide
  have hdescent : baseEnd_2876658 < baseStart_2876658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876767 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2876767 : Nat := 118140960795 + 2876767 * 2 ^ 59
def prefixEnd_2876767 : Nat := 4983230072969 + 3 ^ 40 * 2876767 * 2
def baseEnd_2876767 : Nat := 1477164201992851369582495

theorem tailTrace_2876767 : CollatzResearch.WordTrace tailWord_2876767 prefixEnd_2876767 1477164201992851369582495 := by
  unfold tailWord_2876767
  simp only [CollatzResearch.WordTrace]
  refine ⟨104924312368971946533308555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69949541579314631022205703 104924312368971946533308555)
  ·
    refine ⟨157386468553457919799962833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104924312368971946533308555 157386468553457919799962833)
    ·
      refine ⟨118039851415093439849972125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157386468553457919799962833 118039851415093439849972125)
      ·
        refine ⟨44264944280660039943739547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118039851415093439849972125 44264944280660039943739547)
        ·
          refine ⟨66397416420990059915609321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44264944280660039943739547 66397416420990059915609321)
          ·
            refine ⟨49798062315742544936706991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66397416420990059915609321 49798062315742544936706991)
            ·
              refine ⟨74697093473613817405060487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49798062315742544936706991 74697093473613817405060487)
              ·
                refine ⟨112045640210420726107590731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74697093473613817405060487 112045640210420726107590731)
                ·
                  refine ⟨168068460315631089161386097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112045640210420726107590731 168068460315631089161386097)
                  ·
                    refine ⟨126051345236723316871039573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168068460315631089161386097 126051345236723316871039573)
                    ·
                      refine ⟨1477164201992851369582495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 126051345236723316871039573 1477164201992851369582495)
                      ·
                        rfl

theorem cell23_2876767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2876767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876767 prefixEnd_2876767 := by exact prefixLift 2876767
  have htrace : WordTrace (prefixWord ++ tailWord_2876767) baseStart_2876767 baseEnd_2876767 := by
    simpa [prefixWord, tailWord_2876767, baseEnd_2876767] using wordTrace_append hprefix tailTrace_2876767
  have hstable : (prefixWord ++ tailWord_2876767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876767).length < 2 ^ (prefixWord ++ tailWord_2876767).sum := by decide
  have hdescent : baseEnd_2876767 < baseStart_2876767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876777 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_2876777 : Nat := 118140960795 + 2876777 * 2 ^ 59
def prefixEnd_2876777 : Nat := 4983230072969 + 3 ^ 40 * 2876777 * 2
def baseEnd_2876777 : Nat := 492389778933132110152483

theorem tailTrace_2876777 : CollatzResearch.WordTrace tailWord_2876777 prefixEnd_2876777 492389778933132110152483 := by
  unfold tailWord_2876777
  simp only [CollatzResearch.WordTrace]
  refine ⟨104924677098935718241172585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69949784732623812160781723 104924677098935718241172585)
  ·
    refine ⟨78693507824201788680879439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104924677098935718241172585 78693507824201788680879439)
    ·
      refine ⟨118040261736302683021319159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78693507824201788680879439 118040261736302683021319159)
      ·
        refine ⟨177060392604454024531978739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118040261736302683021319159 177060392604454024531978739)
        ·
          refine ⟨265590588906681036797968109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177060392604454024531978739 265590588906681036797968109)
          ·
            refine ⟨99596470840005388799238041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265590588906681036797968109 99596470840005388799238041)
            ·
              refine ⟨74697353130004041599428531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99596470840005388799238041 74697353130004041599428531)
              ·
                refine ⟨112046029695006062399142797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74697353130004041599428531 112046029695006062399142797)
                ·
                  refine ⟨42017261135627273399678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112046029695006062399142797 42017261135627273399678549)
                  ·
                    refine ⟨492389778933132110152483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42017261135627273399678549 492389778933132110152483)
                    ·
                      rfl

theorem cell23_2876777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_2876777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876777 prefixEnd_2876777 := by exact prefixLift 2876777
  have htrace : WordTrace (prefixWord ++ tailWord_2876777) baseStart_2876777 baseEnd_2876777 := by
    simpa [prefixWord, tailWord_2876777, baseEnd_2876777] using wordTrace_append hprefix tailTrace_2876777
  have hstable : (prefixWord ++ tailWord_2876777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876777).length < 2 ^ (prefixWord ++ tailWord_2876777).sum := by decide
  have hdescent : baseEnd_2876777 < baseStart_2876777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876778 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2876778 : Nat := 118140960795 + 2876778 * 2 ^ 59
def prefixEnd_2876778 : Nat := 4983230072969 + 3 ^ 40 * 2876778 * 2
def baseEnd_2876778 : Nat := 1477169850280050826544945

theorem tailTrace_2876778 : CollatzResearch.WordTrace tailWord_2876778 prefixEnd_2876778 1477169850280050826544945 := by
  unfold tailWord_2876778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26231178392983023852989747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69949809047954730274639325 26231178392983023852989747)
  ·
    refine ⟨39346767589474535779484621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26231178392983023852989747 39346767589474535779484621)
    ·
      refine ⟨14755037846052950917306733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39346767589474535779484621 14755037846052950917306733)
      ·
        refine ⟨5533139192269856593990025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14755037846052950917306733 5533139192269856593990025)
        ·
          refine ⟨4149854394202392445492519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5533139192269856593990025 4149854394202392445492519)
          ·
            refine ⟨6224781591303588668238779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149854394202392445492519 6224781591303588668238779)
            ·
              refine ⟨9337172386955383002358169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224781591303588668238779 9337172386955383002358169)
              ·
                refine ⟨7002879290216537251768627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9337172386955383002358169 7002879290216537251768627)
                ·
                  refine ⟨10504318935324805877652941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002879290216537251768627 10504318935324805877652941)
                  ·
                    refine ⟨3939119600746802204119853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10504318935324805877652941 3939119600746802204119853)
                    ·
                      refine ⟨1477169850280050826544945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3939119600746802204119853 1477169850280050826544945)
                      ·
                        rfl

theorem cell23_2876778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2876778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876778 prefixEnd_2876778 := by exact prefixLift 2876778
  have htrace : WordTrace (prefixWord ++ tailWord_2876778) baseStart_2876778 baseEnd_2876778 := by
    simpa [prefixWord, tailWord_2876778, baseEnd_2876778] using wordTrace_append hprefix tailTrace_2876778
  have hstable : (prefixWord ++ tailWord_2876778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876778).length < 2 ^ (prefixWord ++ tailWord_2876778).sum := by decide
  have hdescent : baseEnd_2876778 < baseStart_2876778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876782 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2876782 : Nat := 118140960795 + 2876782 * 2 ^ 59
def prefixEnd_2876782 : Nat := 4983230072969 + 3 ^ 40 * 2876782 * 2
def baseEnd_2876782 : Nat := 1477171904202668810894927

theorem tailTrace_2876782 : CollatzResearch.WordTrace tailWord_2876782 prefixEnd_2876782 1477171904202668810894927 := by
  unfold tailWord_2876782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13115607432989700511888075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69949906309278402730069733 13115607432989700511888075)
  ·
    refine ⟨19673411149484550767832113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13115607432989700511888075 19673411149484550767832113)
    ·
      refine ⟨14755058362113413075874085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19673411149484550767832113 14755058362113413075874085)
      ·
        refine ⟨2766573442896264951726391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14755058362113413075874085 2766573442896264951726391)
        ·
          refine ⟨4149860164344397427589587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766573442896264951726391 4149860164344397427589587)
          ·
            refine ⟨6224790246516596141384381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149860164344397427589587 6224790246516596141384381)
            ·
              refine ⟨2334296342443723553019143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6224790246516596141384381 2334296342443723553019143)
              ·
                refine ⟨3501444513665585329528715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334296342443723553019143 3501444513665585329528715)
                ·
                  refine ⟨5252166770498377994293073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501444513665585329528715 5252166770498377994293073)
                  ·
                    refine ⟨3939125077873783495719805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252166770498377994293073 3939125077873783495719805)
                    ·
                      refine ⟨1477171904202668810894927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3939125077873783495719805 1477171904202668810894927)
                      ·
                        rfl

theorem cell23_2876782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2876782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876782 prefixEnd_2876782 := by exact prefixLift 2876782
  have htrace : WordTrace (prefixWord ++ tailWord_2876782) baseStart_2876782 baseEnd_2876782 := by
    simpa [prefixWord, tailWord_2876782, baseEnd_2876782] using wordTrace_append hprefix tailTrace_2876782
  have hstable : (prefixWord ++ tailWord_2876782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876782).length < 2 ^ (prefixWord ++ tailWord_2876782).sum := by decide
  have hdescent : baseEnd_2876782 < baseStart_2876782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876864 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_2876864 : Nat := 118140960795 + 2876864 * 2 ^ 59
def prefixEnd_2876864 : Nat := 4983230072969 + 3 ^ 40 * 2876864 * 2
def baseEnd_2876864 : Nat := 1477214009616337490069549

theorem tailTrace_2876864 : CollatzResearch.WordTrace tailWord_2876864 prefixEnd_2876864 1477214009616337490069549 := by
  unfold tailWord_2876864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52463925124810266049794823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69951900166413688066393097 52463925124810266049794823)
  ·
    refine ⟨78695887687215399074692235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52463925124810266049794823 78695887687215399074692235)
    ·
      refine ⟨118043831530823098612038353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78695887687215399074692235 118043831530823098612038353)
      ·
        refine ⟨88532873648117323959028765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118043831530823098612038353 88532873648117323959028765)
        ·
          refine ⟨33199827618043996484635787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88532873648117323959028765 33199827618043996484635787)
          ·
            refine ⟨49799741427065994726953681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33199827618043996484635787 49799741427065994726953681)
            ·
              refine ⟨37349806070299496045215261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49799741427065994726953681 37349806070299496045215261)
              ·
                refine ⟨14006177276362311016955723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37349806070299496045215261 14006177276362311016955723)
                ·
                  refine ⟨21009265914543466525433585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14006177276362311016955723 21009265914543466525433585)
                  ·
                    refine ⟨15756949435907599894075189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21009265914543466525433585 15756949435907599894075189)
                    ·
                      refine ⟨1477214009616337490069549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15756949435907599894075189 1477214009616337490069549)
                      ·
                        rfl

theorem cell23_2876864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_2876864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876864 prefixEnd_2876864 := by exact prefixLift 2876864
  have htrace : WordTrace (prefixWord ++ tailWord_2876864) baseStart_2876864 baseEnd_2876864 := by
    simpa [prefixWord, tailWord_2876864, baseEnd_2876864] using wordTrace_append hprefix tailTrace_2876864
  have hstable : (prefixWord ++ tailWord_2876864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876864).length < 2 ^ (prefixWord ++ tailWord_2876864).sum := by decide
  have hdescent : baseEnd_2876864 < baseStart_2876864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876868 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2876868 : Nat := 118140960795 + 2876868 * 2 ^ 59
def prefixEnd_2876868 : Nat := 4983230072969 + 3 ^ 40 * 2876868 * 2
def baseEnd_2876868 : Nat := 1477216063538955474419531

theorem tailTrace_2876868 : CollatzResearch.WordTrace tailWord_2876868 prefixEnd_2876868 1477216063538955474419531 := by
  unfold tailWord_2876868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52463998070803020391367629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69951997427737360521823505 52463998070803020391367629)
  ·
    refine ⟨19673999276551132646762861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52463998070803020391367629 19673999276551132646762861)
    ·
      refine ⟨7377749728706674742536073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19673999276551132646762861 7377749728706674742536073)
      ·
        refine ⟨5533312296530006056902055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7377749728706674742536073 5533312296530006056902055)
        ·
          refine ⟨8299968444795009085353083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533312296530006056902055 8299968444795009085353083)
          ·
            refine ⟨12449952667192513628029625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8299968444795009085353083 12449952667192513628029625)
            ·
              refine ⟨9337464500394385221022219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12449952667192513628029625 9337464500394385221022219)
              ·
                refine ⟨14006196750591577831533329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9337464500394385221022219 14006196750591577831533329)
                ·
                  refine ⟨10504647562943683373649997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14006196750591577831533329 10504647562943683373649997)
                  ·
                    refine ⟨3939242836103881265118749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10504647562943683373649997 3939242836103881265118749)
                    ·
                      refine ⟨1477216063538955474419531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3939242836103881265118749 1477216063538955474419531)
                      ·
                        rfl

theorem cell23_2876868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2876868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876868 prefixEnd_2876868 := by exact prefixLift 2876868
  have htrace : WordTrace (prefixWord ++ tailWord_2876868) baseStart_2876868 baseEnd_2876868 := by
    simpa [prefixWord, tailWord_2876868, baseEnd_2876868] using wordTrace_append hprefix tailTrace_2876868
  have hstable : (prefixWord ++ tailWord_2876868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876868).length < 2 ^ (prefixWord ++ tailWord_2876868).sum := by decide
  have hdescent : baseEnd_2876868 < baseStart_2876868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876911 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_2876911 : Nat := 118140960795 + 2876911 * 2 ^ 59
def prefixEnd_2876911 : Nat := 4983230072969 + 3 ^ 40 * 2876911 * 2
def baseEnd_2876911 : Nat := 1477238143207098806181833

theorem tailTrace_2876911 : CollatzResearch.WordTrace tailWord_2876911 prefixEnd_2876911 1477238143207098806181833 := by
  unfold tailWord_2876911
  simp only [CollatzResearch.WordTrace]
  refine ⟨104929564480450259126550587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69953042986966839417700391 104929564480450259126550587)
  ·
    refine ⟨157394346720675388689825881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104929564480450259126550587 157394346720675388689825881)
    ·
      refine ⟨118045760040506541517369411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157394346720675388689825881 118045760040506541517369411)
      ·
        refine ⟨177068640060759812276054117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118045760040506541517369411 177068640060759812276054117)
        ·
          refine ⟨33200370011392464801760147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177068640060759812276054117 33200370011392464801760147)
          ·
            refine ⟨49800555017088697202640221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33200370011392464801760147 49800555017088697202640221)
            ·
              refine ⟨18675208131408261450990083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49800555017088697202640221 18675208131408261450990083)
              ·
                refine ⟨28012812197112392176485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18675208131408261450990083 28012812197112392176485125)
                ·
                  refine ⟨5252402286958573533090961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28012812197112392176485125 5252402286958573533090961)
                  ·
                    refine ⟨3939301715218930149818221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5252402286958573533090961 3939301715218930149818221)
                    ·
                      refine ⟨1477238143207098806181833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3939301715218930149818221 1477238143207098806181833)
                      ·
                        rfl

theorem cell23_2876911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_2876911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876911 prefixEnd_2876911 := by exact prefixLift 2876911
  have htrace : WordTrace (prefixWord ++ tailWord_2876911) baseStart_2876911 baseEnd_2876911 := by
    simpa [prefixWord, tailWord_2876911, baseEnd_2876911] using wordTrace_append hprefix tailTrace_2876911
  have hstable : (prefixWord ++ tailWord_2876911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876911).length < 2 ^ (prefixWord ++ tailWord_2876911).sum := by decide
  have hdescent : baseEnd_2876911 < baseStart_2876911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876991 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 1, 6]
def baseStart_2876991 : Nat := 118140960795 + 2876991 * 2 ^ 59
def prefixEnd_2876991 : Nat := 4983230072969 + 3 ^ 40 * 2876991 * 2
def baseEnd_2876991 : Nat := 492426407219819497727155

theorem tailTrace_2876991 : CollatzResearch.WordTrace tailWord_2876991 prefixEnd_2876991 492426407219819497727155 := by
  unfold tailWord_2876991
  simp only [CollatzResearch.WordTrace]
  refine ⟨104932482320160432789462827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69954988213440288526308551 104932482320160432789462827)
  ·
    refine ⟨157398723480240649184194241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104932482320160432789462827 157398723480240649184194241)
    ·
      refine ⟨118049042610180486888145681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157398723480240649184194241 118049042610180486888145681)
      ·
        refine ⟨88536781957635365166109261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118049042610180486888145681 88536781957635365166109261)
        ·
          refine ⟨33201293234113261937290973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88536781957635365166109261 33201293234113261937290973)
          ·
            refine ⟨12450484962792473226484115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33201293234113261937290973 12450484962792473226484115)
            ·
              refine ⟨18675727444188709839726173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12450484962792473226484115 18675727444188709839726173)
              ·
                refine ⟨7003397791570766189897315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18675727444188709839726173 7003397791570766189897315)
                ·
                  refine ⟨10505096687356149284845973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003397791570766189897315 10505096687356149284845973)
                  ·
                    refine ⟨492426407219819497727155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10505096687356149284845973 492426407219819497727155)
                    ·
                      rfl

theorem cell23_2876991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_2876991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2876991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2876991 prefixEnd_2876991 := by exact prefixLift 2876991
  have htrace : WordTrace (prefixWord ++ tailWord_2876991) baseStart_2876991 baseEnd_2876991 := by
    simpa [prefixWord, tailWord_2876991, baseEnd_2876991] using wordTrace_append hprefix tailTrace_2876991
  have hstable : (prefixWord ++ tailWord_2876991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876991).length < 2 ^ (prefixWord ++ tailWord_2876991).sum := by decide
  have hdescent : baseEnd_2876991 < baseStart_2876991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877015 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_2877015 : Nat := 118140960795 + 2877015 * 2 ^ 59
def prefixEnd_2877015 : Nat := 4983230072969 + 3 ^ 40 * 2877015 * 2
def baseEnd_2877015 : Nat := 1477291545195166399281355

theorem tailTrace_2877015 : CollatzResearch.WordTrace tailWord_2877015 prefixEnd_2877015 1477291545195166399281355 := by
  unfold tailWord_2877015
  simp only [CollatzResearch.WordTrace]
  refine ⟨104933357672073484888336499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69955571781382323258890999 104933357672073484888336499)
  ·
    refine ⟨157400036508110227332504749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104933357672073484888336499 157400036508110227332504749)
    ·
      refine ⟨59025013690541335249689281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157400036508110227332504749 59025013690541335249689281)
      ·
        refine ⟨44268760267906001437266961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59025013690541335249689281 44268760267906001437266961)
        ·
          refine ⟨33201570200929501077950221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44268760267906001437266961 33201570200929501077950221)
          ·
            refine ⟨12450588825348562904231333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33201570200929501077950221 12450588825348562904231333)
            ·
              refine ⟨2334485404752855544543375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12450588825348562904231333 2334485404752855544543375)
              ·
                refine ⟨3501728107129283316815063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334485404752855544543375 3501728107129283316815063)
                ·
                  refine ⟨5252592160693924975222595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501728107129283316815063 5252592160693924975222595)
                  ·
                    refine ⟨7878888241040887462833893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5252592160693924975222595 7878888241040887462833893)
                    ·
                      refine ⟨1477291545195166399281355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7878888241040887462833893 1477291545195166399281355)
                      ·
                        rfl

theorem cell23_2877015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_2877015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877015 prefixEnd_2877015 := by exact prefixLift 2877015
  have htrace : WordTrace (prefixWord ++ tailWord_2877015) baseStart_2877015 baseEnd_2877015 := by
    simpa [prefixWord, tailWord_2877015, baseEnd_2877015] using wordTrace_append hprefix tailTrace_2877015
  have hstable : (prefixWord ++ tailWord_2877015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877015).length < 2 ^ (prefixWord ++ tailWord_2877015).sum := by decide
  have hdescent : baseEnd_2877015 < baseStart_2877015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877032 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2877032 : Nat := 118140960795 + 2877032 * 2 ^ 59
def prefixEnd_2877032 : Nat := 4983230072969 + 3 ^ 40 * 2877032 * 2
def baseEnd_2877032 : Nat := 1477300274366292832768777

theorem tailTrace_2877032 : CollatzResearch.WordTrace tailWord_2877032 prefixEnd_2877032 1477300274366292832768777 := by
  unfold tailWord_2877032
  simp only [CollatzResearch.WordTrace]
  refine ⟨52466988856505948395852675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69955985142007931194470233 52466988856505948395852675)
  ·
    refine ⟨78700483284758922593779013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52466988856505948395852675 78700483284758922593779013)
    ·
      refine ⟨14756340615892297986333565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78700483284758922593779013 14756340615892297986333565)
      ·
        refine ⟨5533627730959611744875087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14756340615892297986333565 5533627730959611744875087)
        ·
          refine ⟨8300441596439417617312631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533627730959611744875087 8300441596439417617312631)
          ·
            refine ⟨12450662394659126425968947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300441596439417617312631 12450662394659126425968947)
            ·
              refine ⟨18675993591988689638953421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12450662394659126425968947 18675993591988689638953421)
              ·
                refine ⟨7003497596995758614607533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18675993591988689638953421 7003497596995758614607533)
                ·
                  refine ⟨2626311598873409480477825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7003497596995758614607533 2626311598873409480477825)
                  ·
                    refine ⟨1969733699155057110358369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2626311598873409480477825 1969733699155057110358369)
                    ·
                      refine ⟨1477300274366292832768777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969733699155057110358369 1477300274366292832768777)
                      ·
                        rfl

theorem cell23_2877032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2877032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877032 prefixEnd_2877032 := by exact prefixLift 2877032
  have htrace : WordTrace (prefixWord ++ tailWord_2877032) baseStart_2877032 baseEnd_2877032 := by
    simpa [prefixWord, tailWord_2877032, baseEnd_2877032] using wordTrace_append hprefix tailTrace_2877032
  have hstable : (prefixWord ++ tailWord_2877032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877032).length < 2 ^ (prefixWord ++ tailWord_2877032).sum := by decide
  have hdescent : baseEnd_2877032 < baseStart_2877032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877042 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_2877042 : Nat := 118140960795 + 2877042 * 2 ^ 59
def prefixEnd_2877042 : Nat := 4983230072969 + 3 ^ 40 * 2877042 * 2
def baseEnd_2877042 : Nat := 492435136390945931214577

theorem tailTrace_2877042 : CollatzResearch.WordTrace tailWord_2877042 prefixEnd_2877042 492435136390945931214577 := by
  unfold tailWord_2877042
  simp only [CollatzResearch.WordTrace]
  refine ⟨26233585610743917124892345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69956228295317112333046253 26233585610743917124892345)
  ·
    refine ⟨19675189208057937843669259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26233585610743917124892345 19675189208057937843669259)
    ·
      refine ⟨29512783812086906765503889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19675189208057937843669259 29512783812086906765503889)
      ·
        refine ⟨22134587859065180074127917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29512783812086906765503889 22134587859065180074127917)
        ·
          refine ⟨8300470447149442527797969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22134587859065180074127917 8300470447149442527797969)
          ·
            refine ⟨6225352835362081895848477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8300470447149442527797969 6225352835362081895848477)
            ·
              refine ⟨2334507313260780710943179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6225352835362081895848477 2334507313260780710943179)
              ·
                refine ⟨3501760969891171066414769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334507313260780710943179 3501760969891171066414769)
                ·
                  refine ⟨2626320727418378299811077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501760969891171066414769 2626320727418378299811077)
                  ·
                    refine ⟨492435136390945931214577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2626320727418378299811077 492435136390945931214577)
                    ·
                      rfl

theorem cell23_2877042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_2877042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877042 prefixEnd_2877042 := by exact prefixLift 2877042
  have htrace : WordTrace (prefixWord ++ tailWord_2877042) baseStart_2877042 baseEnd_2877042 := by
    simpa [prefixWord, tailWord_2877042, baseEnd_2877042] using wordTrace_append hprefix tailTrace_2877042
  have hstable : (prefixWord ++ tailWord_2877042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877042).length < 2 ^ (prefixWord ++ tailWord_2877042).sum := by decide
  have hdescent : baseEnd_2877042 < baseStart_2877042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877045 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2877045 : Nat := 118140960795 + 2877045 * 2 ^ 59
def prefixEnd_2877045 : Nat := 4983230072969 + 3 ^ 40 * 2877045 * 2
def baseEnd_2877045 : Nat := 1477306949614801281906217

theorem tailTrace_2877045 : CollatzResearch.WordTrace tailWord_2877045 prefixEnd_2877045 1477306949614801281906217 := by
  unfold tailWord_2877045
  simp only [CollatzResearch.WordTrace]
  refine ⟨104934451861964800011928589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69956301241309866674619059 104934451861964800011928589)
  ·
    refine ⟨39350419448236800004473221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104934451861964800011928589 39350419448236800004473221)
    ·
      refine ⟨7378203646544400000838729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39350419448236800004473221 7378203646544400000838729)
      ·
        refine ⟨5533652734908300000629047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7378203646544400000838729 5533652734908300000629047)
        ·
          refine ⟨8300479102362450000943571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5533652734908300000629047 8300479102362450000943571)
          ·
            refine ⟨12450718653543675001415357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8300479102362450000943571 12450718653543675001415357)
            ·
              refine ⟨4669019495078878125530759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12450718653543675001415357 4669019495078878125530759)
              ·
                refine ⟨7003529242618317188296139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669019495078878125530759 7003529242618317188296139)
                ·
                  refine ⟨10505293863927475782444209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003529242618317188296139 10505293863927475782444209)
                  ·
                    refine ⟨7878970397945606836833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10505293863927475782444209 7878970397945606836833157)
                    ·
                      refine ⟨1477306949614801281906217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7878970397945606836833157 1477306949614801281906217)
                      ·
                        rfl

theorem cell23_2877045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2877045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877045 prefixEnd_2877045 := by exact prefixLift 2877045
  have htrace : WordTrace (prefixWord ++ tailWord_2877045) baseStart_2877045 baseEnd_2877045 := by
    simpa [prefixWord, tailWord_2877045, baseEnd_2877045] using wordTrace_append hprefix tailTrace_2877045
  have hstable : (prefixWord ++ tailWord_2877045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877045).length < 2 ^ (prefixWord ++ tailWord_2877045).sum := by decide
  have hdescent : baseEnd_2877045 < baseStart_2877045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877048 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_2877048 : Nat := 118140960795 + 2877048 * 2 ^ 59
def prefixEnd_2877048 : Nat := 4983230072969 + 3 ^ 40 * 2877048 * 2
def baseEnd_2877048 : Nat := 1477308490056764770168703

theorem tailTrace_2877048 : CollatzResearch.WordTrace tailWord_2877048 prefixEnd_2877048 1477308490056764770168703 := by
  unfold tailWord_2877048
  simp only [CollatzResearch.WordTrace]
  refine ⟨52467280640476965762143899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69956374187302621016191865 52467280640476965762143899)
  ·
    refine ⟨78700920960715448643215849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52467280640476965762143899 78700920960715448643215849)
    ·
      refine ⟨59025690720536586482411887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78700920960715448643215849 59025690720536586482411887)
      ·
        refine ⟨88538536080804879723617831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59025690720536586482411887 88538536080804879723617831)
        ·
          refine ⟨132807804121207319585426747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88538536080804879723617831 132807804121207319585426747)
          ·
            refine ⟨199211706181810979378140121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132807804121207319585426747 199211706181810979378140121)
            ·
              refine ⟨149408779636358234533605091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199211706181810979378140121 149408779636358234533605091)
              ·
                refine ⟨224113169454537351800407637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149408779636358234533605091 224113169454537351800407637)
                ·
                  refine ⟨2626326204545359591411027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 224113169454537351800407637 2626326204545359591411027)
                  ·
                    refine ⟨3939489306818039387116541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2626326204545359591411027 3939489306818039387116541)
                    ·
                      refine ⟨1477308490056764770168703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3939489306818039387116541 1477308490056764770168703)
                      ·
                        rfl

theorem cell23_2877048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_2877048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877048 prefixEnd_2877048 := by exact prefixLift 2877048
  have htrace : WordTrace (prefixWord ++ tailWord_2877048) baseStart_2877048 baseEnd_2877048 := by
    simpa [prefixWord, tailWord_2877048, baseEnd_2877048] using wordTrace_append hprefix tailTrace_2877048
  have hstable : (prefixWord ++ tailWord_2877048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877048).length < 2 ^ (prefixWord ++ tailWord_2877048).sum := by decide
  have hdescent : baseEnd_2877048 < baseStart_2877048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877061 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2877061 : Nat := 118140960795 + 2877061 * 2 ^ 59
def prefixEnd_2877061 : Nat := 4983230072969 + 3 ^ 40 * 2877061 * 2
def baseEnd_2877061 : Nat := 1477315165305273219306143

theorem tailTrace_2877061 : CollatzResearch.WordTrace tailWord_2877061 prefixEnd_2877061 1477315165305273219306143 := by
  unfold tailWord_2877061
  simp only [CollatzResearch.WordTrace]
  refine ⟨104935035429906834744511037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69956690286604556496340691 104935035429906834744511037)
  ·
    refine ⟨39350638286215063029191639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104935035429906834744511037 39350638286215063029191639)
    ·
      refine ⟨59025957429322594543787459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39350638286215063029191639 59025957429322594543787459)
      ·
        refine ⟨88538936143983891815681189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59025957429322594543787459 88538936143983891815681189)
        ·
          refine ⟨16601050526996979715440223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88538936143983891815681189 16601050526996979715440223)
          ·
            refine ⟨24901575790495469573160335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16601050526996979715440223 24901575790495469573160335)
            ·
              refine ⟨37352363685743204359740503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24901575790495469573160335 37352363685743204359740503)
              ·
                refine ⟨56028545528614806539610755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37352363685743204359740503 56028545528614806539610755)
                ·
                  refine ⟨84042818292922209809416133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56028545528614806539610755 84042818292922209809416133)
                  ·
                    refine ⟨15758028429922914339265525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84042818292922209809416133 15758028429922914339265525)
                    ·
                      refine ⟨1477315165305273219306143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15758028429922914339265525 1477315165305273219306143)
                      ·
                        rfl

theorem cell23_2877061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2877061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877061 prefixEnd_2877061 := by exact prefixLift 2877061
  have htrace : WordTrace (prefixWord ++ tailWord_2877061) baseStart_2877061 baseEnd_2877061 := by
    simpa [prefixWord, tailWord_2877061, baseEnd_2877061] using wordTrace_append hprefix tailTrace_2877061
  have hstable : (prefixWord ++ tailWord_2877061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877061).length < 2 ^ (prefixWord ++ tailWord_2877061).sum := by decide
  have hdescent : baseEnd_2877061 < baseStart_2877061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877066 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_2877066 : Nat := 118140960795 + 2877066 * 2 ^ 59
def prefixEnd_2877066 : Nat := 4983230072969 + 3 ^ 40 * 2877066 * 2
def baseEnd_2877066 : Nat := 1477317732708545699743621

theorem tailTrace_2877066 : CollatzResearch.WordTrace tailWord_2877066 prefixEnd_2877066 1477317732708545699743621 := by
  unfold tailWord_2877066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26233804448722180149610763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69956811863259147065628701 26233804448722180149610763)
  ·
    refine ⟨39350706673083270224416145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26233804448722180149610763 39350706673083270224416145)
    ·
      refine ⟨29513030004812452668312109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39350706673083270224416145 29513030004812452668312109)
      ·
        refine ⟨11067386251804669750617041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29513030004812452668312109 11067386251804669750617041)
        ·
          refine ⟨8300539688853502312962781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11067386251804669750617041 8300539688853502312962781)
          ·
            refine ⟨3112702383320063367361043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8300539688853502312962781 3112702383320063367361043)
            ·
              refine ⟨4669053574980095051041565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112702383320063367361043 4669053574980095051041565)
              ·
                refine ⟨1750895090617535644140587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4669053574980095051041565 1750895090617535644140587)
                ·
                  refine ⟨2626342635926303466210881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750895090617535644140587 2626342635926303466210881)
                  ·
                    refine ⟨1969756976944727599658161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2626342635926303466210881 1969756976944727599658161)
                    ·
                      refine ⟨1477317732708545699743621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969756976944727599658161 1477317732708545699743621)
                      ·
                        rfl

theorem cell23_2877066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_2877066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877066 prefixEnd_2877066 := by exact prefixLift 2877066
  have htrace : WordTrace (prefixWord ++ tailWord_2877066) baseStart_2877066 baseEnd_2877066 := by
    simpa [prefixWord, tailWord_2877066, baseEnd_2877066] using wordTrace_append hprefix tailTrace_2877066
  have hstable : (prefixWord ++ tailWord_2877066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877066).length < 2 ^ (prefixWord ++ tailWord_2877066).sum := by decide
  have hdescent : baseEnd_2877066 < baseStart_2877066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877081 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_2877081 : Nat := 118140960795 + 2877081 * 2 ^ 59
def prefixEnd_2877081 : Nat := 4983230072969 + 3 ^ 40 * 2877081 * 2
def baseEnd_2877081 : Nat := 492441811639454380352017

theorem tailTrace_2877081 : CollatzResearch.WordTrace tailWord_2877081 prefixEnd_2877081 492441811639454380352017 := by
  unfold tailWord_2877081
  simp only [CollatzResearch.WordTrace]
  refine ⟨104935764889834378160239097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69957176593222918773492731 104935764889834378160239097)
  ·
    refine ⟨78701823667375783620179323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104935764889834378160239097 78701823667375783620179323)
    ·
      refine ⟨118052735501063675430268985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78701823667375783620179323 118052735501063675430268985)
      ·
        refine ⟨88539551625797756572701739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118052735501063675430268985 88539551625797756572701739)
        ·
          refine ⟨132809327438696634859052609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88539551625797756572701739 132809327438696634859052609)
          ·
            refine ⟨99606995579022476144289457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132809327438696634859052609 99606995579022476144289457)
            ·
              refine ⟨74705246684266857108217093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99606995579022476144289457 74705246684266857108217093)
              ·
                refine ⟨14007233753300035707790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74705246684266857108217093 14007233753300035707790705)
                ·
                  refine ⟨10505425314975026780843029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14007233753300035707790705 10505425314975026780843029)
                  ·
                    refine ⟨492441811639454380352017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10505425314975026780843029 492441811639454380352017)
                    ·
                      rfl

theorem cell23_2877081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_2877081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877081 prefixEnd_2877081 := by exact prefixLift 2877081
  have htrace : WordTrace (prefixWord ++ tailWord_2877081) baseStart_2877081 baseEnd_2877081 := by
    simpa [prefixWord, tailWord_2877081, baseEnd_2877081] using wordTrace_append hprefix tailTrace_2877081
  have hstable : (prefixWord ++ tailWord_2877081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877081).length < 2 ^ (prefixWord ++ tailWord_2877081).sum := by decide
  have hdescent : baseEnd_2877081 < baseStart_2877081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877091 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_2877091 : Nat := 118140960795 + 2877091 * 2 ^ 59
def prefixEnd_2877091 : Nat := 4983230072969 + 3 ^ 40 * 2877091 * 2
def baseEnd_2877091 : Nat := 1477330569724908101931005

theorem tailTrace_2877091 : CollatzResearch.WordTrace tailWord_2877091 prefixEnd_2877091 1477330569724908101931005 := by
  unfold tailWord_2877091
  simp only [CollatzResearch.WordTrace]
  refine ⟨104936129619798149868103127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69957419746532099912068751 104936129619798149868103127)
  ·
    refine ⟨157404194429697224802154691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104936129619798149868103127 157404194429697224802154691)
    ·
      refine ⟨236106291644545837203232037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157404194429697224802154691 236106291644545837203232037)
      ·
        refine ⟨44269929683352344475606007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236106291644545837203232037 44269929683352344475606007)
        ·
          refine ⟨66404894525028516713409011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44269929683352344475606007 66404894525028516713409011)
          ·
            refine ⟨99607341787542775070113517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66404894525028516713409011 99607341787542775070113517)
            ·
              refine ⟨37352753170328540651292569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99607341787542775070113517 37352753170328540651292569)
              ·
                refine ⟨28014564877746405488469427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37352753170328540651292569 28014564877746405488469427)
                ·
                  refine ⟨42021847316619608232704141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28014564877746405488469427 42021847316619608232704141)
                  ·
                    refine ⟨15758192743732353087264053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42021847316619608232704141 15758192743732353087264053)
                    ·
                      refine ⟨1477330569724908101931005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15758192743732353087264053 1477330569724908101931005)
                      ·
                        rfl

theorem cell23_2877091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_2877091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877091 prefixEnd_2877091 := by exact prefixLift 2877091
  have htrace : WordTrace (prefixWord ++ tailWord_2877091) baseStart_2877091 baseEnd_2877091 := by
    simpa [prefixWord, tailWord_2877091, baseEnd_2877091] using wordTrace_append hprefix tailTrace_2877091
  have hstable : (prefixWord ++ tailWord_2877091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877091).length < 2 ^ (prefixWord ++ tailWord_2877091).sum := by decide
  have hdescent : baseEnd_2877091 < baseStart_2877091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877145 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 5]
def baseStart_2877145 : Nat := 118140960795 + 2877145 * 2 ^ 59
def prefixEnd_2877145 : Nat := 4983230072969 + 3 ^ 40 * 2877145 * 2
def baseEnd_2877145 : Nat := 164150921964472321183973

theorem tailTrace_2877145 : CollatzResearch.WordTrace tailWord_2877145 prefixEnd_2877145 164150921964472321183973 := by
  unfold tailWord_2877145
  simp only [CollatzResearch.WordTrace]
  refine ⟨104938099161602517090568889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69958732774401678060379259 104938099161602517090568889)
  ·
    refine ⟨78703574371201887817926667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104938099161602517090568889 78703574371201887817926667)
    ·
      refine ⟨118055361556802831726890001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78703574371201887817926667 118055361556802831726890001)
      ·
        refine ⟨88541521167602123795167501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118055361556802831726890001 88541521167602123795167501)
        ·
          refine ⟨33203070437850796423187813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88541521167602123795167501 33203070437850796423187813)
          ·
            refine ⟨6225575707097024329347715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33203070437850796423187813 6225575707097024329347715)
            ·
              refine ⟨9338363560645536494021573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225575707097024329347715 9338363560645536494021573)
              ·
                refine ⟨1750943167621038092629045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9338363560645536494021573 1750943167621038092629045)
                ·
                  refine ⟨164150921964472321183973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1750943167621038092629045 164150921964472321183973)
                  ·
                    rfl

theorem cell23_2877145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 5].length) (baseStart_2877145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877145 prefixEnd_2877145 := by exact prefixLift 2877145
  have htrace : WordTrace (prefixWord ++ tailWord_2877145) baseStart_2877145 baseEnd_2877145 := by
    simpa [prefixWord, tailWord_2877145, baseEnd_2877145] using wordTrace_append hprefix tailTrace_2877145
  have hstable : (prefixWord ++ tailWord_2877145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877145).length < 2 ^ (prefixWord ++ tailWord_2877145).sum := by decide
  have hdescent : baseEnd_2877145 < baseStart_2877145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877195 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 2, 4, 2]
def baseStart_2877195 : Nat := 118140960795 + 2877195 * 2 ^ 59
def prefixEnd_2877195 : Nat := 4983230072969 + 3 ^ 40 * 2877195 * 2
def baseEnd_2877195 : Nat := 1477383971712975695030527

theorem tailTrace_2877195 : CollatzResearch.WordTrace tailWord_2877195 prefixEnd_2877195 1477383971712975695030527 := by
  unfold tailWord_2877195
  simp only [CollatzResearch.WordTrace]
  refine ⟨104939922811421375629889039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69959948540947583753259359 104939922811421375629889039)
  ·
    refine ⟨157409884217132063444833559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104939922811421375629889039 157409884217132063444833559)
    ·
      refine ⟨236114826325698095167250339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157409884217132063444833559 236114826325698095167250339)
      ·
        refine ⟨354172239488547142750875509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236114826325698095167250339 354172239488547142750875509)
        ·
          refine ⟨33203647452051294632894579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354172239488547142750875509 33203647452051294632894579)
          ·
            refine ⟨49805471178076941949341869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33203647452051294632894579 49805471178076941949341869)
            ·
              refine ⟨18677051691778853231003201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49805471178076941949341869 18677051691778853231003201)
              ·
                refine ⟨14007788768834139923252401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18677051691778853231003201 14007788768834139923252401)
                ·
                  refine ⟨10505841576625604942439301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14007788768834139923252401 10505841576625604942439301)
                  ·
                    refine ⟨1969845295617300926707369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10505841576625604942439301 1969845295617300926707369)
                    ·
                      refine ⟨1477383971712975695030527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969845295617300926707369 1477383971712975695030527)
                      ·
                        rfl

theorem cell23_2877195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4, 2].length) (baseStart_2877195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877195 prefixEnd_2877195 := by exact prefixLift 2877195
  have htrace : WordTrace (prefixWord ++ tailWord_2877195) baseStart_2877195 baseEnd_2877195 := by
    simpa [prefixWord, tailWord_2877195, baseEnd_2877195] using wordTrace_append hprefix tailTrace_2877195
  have hstable : (prefixWord ++ tailWord_2877195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877195).length < 2 ^ (prefixWord ++ tailWord_2877195).sum := by decide
  have hdescent : baseEnd_2877195 < baseStart_2877195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877198 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2877198 : Nat := 118140960795 + 2877198 * 2 ^ 59
def prefixEnd_2877198 : Nat := 4983230072969 + 3 ^ 40 * 2877198 * 2
def baseEnd_2877198 : Nat := 1477385512154939183293013

theorem tailTrace_2877198 : CollatzResearch.WordTrace tailWord_2877198 prefixEnd_2877198 1477385512154939183293013 := by
  unfold tailWord_2877198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13117504028801313392781031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69960021486940338094832165 13117504028801313392781031)
  ·
    refine ⟨19676256043201970089171547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13117504028801313392781031 19676256043201970089171547)
    ·
      refine ⟨29514384064802955133757321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19676256043201970089171547 29514384064802955133757321)
      ·
        refine ⟨22135788048602216350317991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29514384064802955133757321 22135788048602216350317991)
        ·
          refine ⟨33203682072903324525476987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22135788048602216350317991 33203682072903324525476987)
          ·
            refine ⟨49805523109354986788215481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33203682072903324525476987 49805523109354986788215481)
            ·
              refine ⟨37354142332016240091161611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49805523109354986788215481 37354142332016240091161611)
              ·
                refine ⟨56031213498024360136742417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37354142332016240091161611 56031213498024360136742417)
                ·
                  refine ⟨42023410123518270102556813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56031213498024360136742417 42023410123518270102556813)
                  ·
                    refine ⟨15758778796319351288458805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42023410123518270102556813 15758778796319351288458805)
                    ·
                      refine ⟨1477385512154939183293013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15758778796319351288458805 1477385512154939183293013)
                      ·
                        rfl

theorem cell23_2877198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2877198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877198 prefixEnd_2877198 := by exact prefixLift 2877198
  have htrace : WordTrace (prefixWord ++ tailWord_2877198) baseStart_2877198 baseEnd_2877198 := by
    simpa [prefixWord, tailWord_2877198, baseEnd_2877198] using wordTrace_append hprefix tailTrace_2877198
  have hstable : (prefixWord ++ tailWord_2877198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877198).length < 2 ^ (prefixWord ++ tailWord_2877198).sum := by decide
  have hdescent : baseEnd_2877198 < baseStart_2877198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877205 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2877205 : Nat := 118140960795 + 2877205 * 2 ^ 59
def prefixEnd_2877205 : Nat := 4983230072969 + 3 ^ 40 * 2877205 * 2
def baseEnd_2877205 : Nat := 492463035506506885301827

theorem tailTrace_2877205 : CollatzResearch.WordTrace tailWord_2877205 prefixEnd_2877205 492463035506506885301827 := by
  unfold tailWord_2877205
  simp only [CollatzResearch.WordTrace]
  refine ⟨104940287541385147337753069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69960191694256764891835379 104940287541385147337753069)
  ·
    refine ⟨39352607828019430251657401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104940287541385147337753069 39352607828019430251657401)
    ·
      refine ⟨29514455871014572688743051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39352607828019430251657401 29514455871014572688743051)
      ·
        refine ⟨44271683806521859033114577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29514455871014572688743051 44271683806521859033114577)
        ·
          refine ⟨33203762854891394274835933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44271683806521859033114577 33203762854891394274835933)
          ·
            refine ⟨12451411070584272853063475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33203762854891394274835933 12451411070584272853063475)
            ·
              refine ⟨18677116605876409279595213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12451411070584272853063475 18677116605876409279595213)
              ·
                refine ⟨7003918727203653479848205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18677116605876409279595213 7003918727203653479848205)
                ·
                  refine ⟨2626469522701370054943077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7003918727203653479848205 2626469522701370054943077)
                  ·
                    refine ⟨492463035506506885301827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2626469522701370054943077 492463035506506885301827)
                    ·
                      rfl

theorem cell23_2877205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2877205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877205 prefixEnd_2877205 := by exact prefixLift 2877205
  have htrace : WordTrace (prefixWord ++ tailWord_2877205) baseStart_2877205 baseEnd_2877205 := by
    simpa [prefixWord, tailWord_2877205, baseEnd_2877205] using wordTrace_append hprefix tailTrace_2877205
  have hstable : (prefixWord ++ tailWord_2877205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877205).length < 2 ^ (prefixWord ++ tailWord_2877205).sum := by decide
  have hdescent : baseEnd_2877205 < baseStart_2877205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877248 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_2877248 : Nat := 118140960795 + 2877248 * 2 ^ 59
def prefixEnd_2877248 : Nat := 4983230072969 + 3 ^ 40 * 2877248 * 2
def baseEnd_2877248 : Nat := 492470395395887995889261

theorem tailTrace_2877248 : CollatzResearch.WordTrace tailWord_2877248 prefixEnd_2877248 492470395395887995889261 := by
  unfold tailWord_2877248
  simp only [CollatzResearch.WordTrace]
  refine ⟨52470927940114682840784199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69961237253486243787712265 52470927940114682840784199)
  ·
    refine ⟨78706391910172024261176299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52470927940114682840784199 78706391910172024261176299)
    ·
      refine ⟨118059587865258036391764449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78706391910172024261176299 118059587865258036391764449)
      ·
        refine ⟨88544690898943527293823337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118059587865258036391764449 88544690898943527293823337)
        ·
          refine ⟨66408518174207645470367503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88544690898943527293823337 66408518174207645470367503)
          ·
            refine ⟨99612777261311468205551255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66408518174207645470367503 99612777261311468205551255)
            ·
              refine ⟨149419165891967202308326883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99612777261311468205551255 149419165891967202308326883)
              ·
                refine ⟨224128748837950803462490325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149419165891967202308326883 224128748837950803462490325)
                ·
                  refine ⟨5253017550889471956152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224128748837950803462490325 5253017550889471956152117)
                  ·
                    refine ⟨492470395395887995889261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5253017550889471956152117 492470395395887995889261)
                    ·
                      rfl

theorem cell23_2877248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_2877248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877248 prefixEnd_2877248 := by exact prefixLift 2877248
  have htrace : WordTrace (prefixWord ++ tailWord_2877248) baseStart_2877248 baseEnd_2877248 := by
    simpa [prefixWord, tailWord_2877248, baseEnd_2877248] using wordTrace_append hprefix tailTrace_2877248
  have hstable : (prefixWord ++ tailWord_2877248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877248).length < 2 ^ (prefixWord ++ tailWord_2877248).sum := by decide
  have hdescent : baseEnd_2877248 < baseStart_2877248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877282 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2877282 : Nat := 118140960795 + 2877282 * 2 ^ 59
def prefixEnd_2877282 : Nat := 4983230072969 + 3 ^ 40 * 2877282 * 2
def baseEnd_2877282 : Nat := 492476214843305618214209

theorem tailTrace_2877282 : CollatzResearch.WordTrace tailWord_2877282 prefixEnd_2877282 492476214843305618214209 := by
  unfold tailWord_2877282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26235773990526547372076525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69962063974737459658870733 26235773990526547372076525)
  ·
    refine ⟨9838415246447455264528697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26235773990526547372076525 9838415246447455264528697)
    ·
      refine ⟨7378811434835591448396523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9838415246447455264528697 7378811434835591448396523)
      ·
        refine ⟨11068217152253387172594785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378811434835591448396523 11068217152253387172594785)
        ·
          refine ⟨8301162864190040379446089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11068217152253387172594785 8301162864190040379446089)
          ·
            refine ⟨6225872148142530284584567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8301162864190040379446089 6225872148142530284584567)
            ·
              refine ⟨9338808222213795426876851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225872148142530284584567 9338808222213795426876851)
              ·
                refine ⟨14008212333320693140315277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338808222213795426876851 14008212333320693140315277)
                ·
                  refine ⟨5253079624995259927618229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14008212333320693140315277 5253079624995259927618229)
                  ·
                    refine ⟨492476214843305618214209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5253079624995259927618229 492476214843305618214209)
                    ·
                      rfl

theorem cell23_2877282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2877282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877282 prefixEnd_2877282 := by exact prefixLift 2877282
  have htrace : WordTrace (prefixWord ++ tailWord_2877282) baseStart_2877282 baseEnd_2877282 := by
    simpa [prefixWord, tailWord_2877282, baseEnd_2877282] using wordTrace_append hprefix tailTrace_2877282
  have hstable : (prefixWord ++ tailWord_2877282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877282).length < 2 ^ (prefixWord ++ tailWord_2877282).sum := by decide
  have hdescent : baseEnd_2877282 < baseStart_2877282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877312 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_2877312 : Nat := 118140960795 + 2877312 * 2 ^ 59
def prefixEnd_2877312 : Nat := 4983230072969 + 3 ^ 40 * 2877312 * 2
def baseEnd_2877312 : Nat := 492481349649850579089163

theorem tailTrace_2877312 : CollatzResearch.WordTrace tailWord_2877312 prefixEnd_2877312 492481349649850579089163 := by
  unfold tailWord_2877312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52472095075998752305949095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69962793434665003074598793 52472095075998752305949095)
  ·
    refine ⟨78708142613998128458923643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52472095075998752305949095 78708142613998128458923643)
    ·
      refine ⟨118062213920997192688385465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78708142613998128458923643 118062213920997192688385465)
      ·
        refine ⟨88546660440747894516289099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118062213920997192688385465 88546660440747894516289099)
        ·
          refine ⟨132819990661121841774433649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88546660440747894516289099 132819990661121841774433649)
          ·
            refine ⟨99614992995841381330825237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132819990661121841774433649 99614992995841381330825237)
            ·
              refine ⟨4669452796680064749882433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99614992995841381330825237 4669452796680064749882433)
              ·
                refine ⟨3502089597510048562411825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669452796680064749882433 3502089597510048562411825)
                ·
                  refine ⟨2626567198132536421808869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3502089597510048562411825 2626567198132536421808869)
                  ·
                    refine ⟨492481349649850579089163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2626567198132536421808869 492481349649850579089163)
                    ·
                      rfl

theorem cell23_2877312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_2877312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877312 prefixEnd_2877312 := by exact prefixLift 2877312
  have htrace : WordTrace (prefixWord ++ tailWord_2877312) baseStart_2877312 baseEnd_2877312 := by
    simpa [prefixWord, tailWord_2877312, baseEnd_2877312] using wordTrace_append hprefix tailTrace_2877312
  have hstable : (prefixWord ++ tailWord_2877312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877312).length < 2 ^ (prefixWord ++ tailWord_2877312).sum := by decide
  have hdescent : baseEnd_2877312 < baseStart_2877312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877313 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2877313 : Nat := 118140960795 + 2877313 * 2 ^ 59
def prefixEnd_2877313 : Nat := 4983230072969 + 3 ^ 40 * 2877313 * 2
def baseEnd_2877313 : Nat := 1477444562430206233354985

theorem tailTrace_2877313 : CollatzResearch.WordTrace tailWord_2877313 prefixEnd_2877313 1477444562430206233354985 := by
  unfold tailWord_2877313
  simp only [CollatzResearch.WordTrace]
  refine ⟨104944226624993881782684593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69962817749995921188456395 104944226624993881782684593)
  ·
    refine ⟨78708169968745411337013445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104944226624993881782684593 78708169968745411337013445)
    ·
      refine ⟨14757781869139764625690021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78708169968745411337013445 14757781869139764625690021)
      ·
        refine ⟨2767084100463705867316879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14757781869139764625690021 2767084100463705867316879)
        ·
          refine ⟨4150626150695558800975319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767084100463705867316879 4150626150695558800975319)
          ·
            refine ⟨6225939226043338201462979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150626150695558800975319 6225939226043338201462979)
            ·
              refine ⟨9338908839065007302194469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6225939226043338201462979 9338908839065007302194469)
              ·
                refine ⟨1751045407324688869161463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9338908839065007302194469 1751045407324688869161463)
                ·
                  refine ⟨2626568110987033303742195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751045407324688869161463 2626568110987033303742195)
                  ·
                    refine ⟨3939852166480549955613293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2626568110987033303742195 3939852166480549955613293)
                    ·
                      refine ⟨1477444562430206233354985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3939852166480549955613293 1477444562430206233354985)
                      ·
                        rfl

theorem cell23_2877313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2877313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877313 prefixEnd_2877313 := by exact prefixLift 2877313
  have htrace : WordTrace (prefixWord ++ tailWord_2877313) baseStart_2877313 baseEnd_2877313 := by
    simpa [prefixWord, tailWord_2877313, baseEnd_2877313] using wordTrace_append hprefix tailTrace_2877313
  have hstable : (prefixWord ++ tailWord_2877313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877313).length < 2 ^ (prefixWord ++ tailWord_2877313).sum := by decide
  have hdescent : baseEnd_2877313 < baseStart_2877313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_2877328 : Nat := 118140960795 + 2877328 * 2 ^ 59
def prefixEnd_2877328 : Nat := 4983230072969 + 3 ^ 40 * 2877328 * 2
def baseEnd_2877328 : Nat := 1477452264640023674667415

theorem tailTrace_2877328 : CollatzResearch.WordTrace tailWord_2877328 prefixEnd_2877328 1477452264640023674667415 := by
  unfold tailWord_2877328
  simp only [CollatzResearch.WordTrace]
  refine ⟨52472386859969769672240319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69963182479959692896320425 52472386859969769672240319)
  ·
    refine ⟨78708580289954654508360479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52472386859969769672240319 78708580289954654508360479)
    ·
      refine ⟨118062870434931981762540719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78708580289954654508360479 118062870434931981762540719)
      ·
        refine ⟨177094305652397972643811079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118062870434931981762540719 177094305652397972643811079)
        ·
          refine ⟨265641458478596958965716619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177094305652397972643811079 265641458478596958965716619)
          ·
            refine ⟨398462187717895438448574929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265641458478596958965716619 398462187717895438448574929)
            ·
              refine ⟨298846640788421578836431197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398462187717895438448574929 298846640788421578836431197)
              ·
                refine ⟨112067490295658092063661699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298846640788421578836431197 112067490295658092063661699)
                ·
                  refine ⟨168101235443487138095492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112067490295658092063661699 168101235443487138095492549)
                  ·
                    refine ⟨31518981645653838392904853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168101235443487138095492549 31518981645653838392904853)
                    ·
                      refine ⟨1477452264640023674667415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31518981645653838392904853 1477452264640023674667415)
                      ·
                        rfl

theorem cell23_2877328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_2877328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877328 prefixEnd_2877328 := by exact prefixLift 2877328
  have htrace : WordTrace (prefixWord ++ tailWord_2877328) baseStart_2877328 baseEnd_2877328 := by
    simpa [prefixWord, tailWord_2877328, baseEnd_2877328] using wordTrace_append hprefix tailTrace_2877328
  have hstable : (prefixWord ++ tailWord_2877328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877328).length < 2 ^ (prefixWord ++ tailWord_2877328).sum := by decide
  have hdescent : baseEnd_2877328 < baseStart_2877328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877332 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2877332 : Nat := 118140960795 + 2877332 * 2 ^ 59
def prefixEnd_2877332 : Nat := 4983230072969 + 3 ^ 40 * 2877332 * 2
def baseEnd_2877332 : Nat := 1477454318562641659017397

theorem tailTrace_2877332 : CollatzResearch.WordTrace tailWord_2877332 prefixEnd_2877332 1477454318562641659017397 := by
  unfold tailWord_2877332
  simp only [CollatzResearch.WordTrace]
  refine ⟨52472459805962524013813125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69963279741283365351750833 52472459805962524013813125)
  ·
    refine ⟨9838586213617973252589961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52472459805962524013813125 9838586213617973252589961)
    ·
      refine ⟨7378939660213479939442471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9838586213617973252589961 7378939660213479939442471)
      ·
        refine ⟨11068409490320219909163707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378939660213479939442471 11068409490320219909163707)
        ·
          refine ⟨16602614235480329863745561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11068409490320219909163707 16602614235480329863745561)
          ·
            refine ⟨12451960676610247397809171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16602614235480329863745561 12451960676610247397809171)
            ·
              refine ⟨18677941014915371096713757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12451960676610247397809171 18677941014915371096713757)
              ·
                refine ⟨7004227880593264161267659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18677941014915371096713757 7004227880593264161267659)
                ·
                  refine ⟨10506341820889896241901489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004227880593264161267659 10506341820889896241901489)
                  ·
                    refine ⟨7879756365667422181426117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10506341820889896241901489 7879756365667422181426117)
                    ·
                      refine ⟨1477454318562641659017397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7879756365667422181426117 1477454318562641659017397)
                      ·
                        rfl

theorem cell23_2877332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2877332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877332 prefixEnd_2877332 := by exact prefixLift 2877332
  have htrace : WordTrace (prefixWord ++ tailWord_2877332) baseStart_2877332 baseEnd_2877332 := by
    simpa [prefixWord, tailWord_2877332, baseEnd_2877332] using wordTrace_append hprefix tailTrace_2877332
  have hstable : (prefixWord ++ tailWord_2877332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877332).length < 2 ^ (prefixWord ++ tailWord_2877332).sum := by decide
  have hdescent : baseEnd_2877332 < baseStart_2877332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877396 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_2877396 : Nat := 118140960795 + 2877396 * 2 ^ 59
def prefixEnd_2877396 : Nat := 4983230072969 + 3 ^ 40 * 2877396 * 2
def baseEnd_2877396 : Nat := 1477487181324529408617103

theorem tailTrace_2877396 : CollatzResearch.WordTrace tailWord_2877396 prefixEnd_2877396 1477487181324529408617103 := by
  unfold tailWord_2877396
  simp only [CollatzResearch.WordTrace]
  refine ⟨52473626941846593478978021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69964835922462124638637361 52473626941846593478978021)
  ·
    refine ⟨9838805051596236277308379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52473626941846593478978021 9838805051596236277308379)
    ·
      refine ⟨14758207577394354415962569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9838805051596236277308379 14758207577394354415962569)
      ·
        refine ⟨11068655683045765811971927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14758207577394354415962569 11068655683045765811971927)
        ·
          refine ⟨16602983524568648717957891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11068655683045765811971927 16602983524568648717957891)
          ·
            refine ⟨24904475286852973076936837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16602983524568648717957891 24904475286852973076936837)
            ·
              refine ⟨4669589116284932451925657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24904475286852973076936837 4669589116284932451925657)
              ·
                refine ⟨3502191837213699338944243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669589116284932451925657 3502191837213699338944243)
                ·
                  refine ⟨5253287755820549008416365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502191837213699338944243 5253287755820549008416365)
                  ·
                    refine ⟨1969982908432705878156137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5253287755820549008416365 1969982908432705878156137)
                    ·
                      refine ⟨1477487181324529408617103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969982908432705878156137 1477487181324529408617103)
                      ·
                        rfl

theorem cell23_2877396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_2877396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877396 prefixEnd_2877396 := by exact prefixLift 2877396
  have htrace : WordTrace (prefixWord ++ tailWord_2877396) baseStart_2877396 baseEnd_2877396 := by
    simpa [prefixWord, tailWord_2877396, baseEnd_2877396] using wordTrace_append hprefix tailTrace_2877396
  have hstable : (prefixWord ++ tailWord_2877396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877396).length < 2 ^ (prefixWord ++ tailWord_2877396).sum := by decide
  have hdescent : baseEnd_2877396 < baseStart_2877396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877404 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2877404 : Nat := 118140960795 + 2877404 * 2 ^ 59
def prefixEnd_2877404 : Nat := 4983230072969 + 3 ^ 40 * 2877404 * 2
def baseEnd_2877404 : Nat := 1477491289169765377317067

theorem tailTrace_2877404 : CollatzResearch.WordTrace tailWord_2877404 prefixEnd_2877404 1477491289169765377317067 := by
  unfold tailWord_2877404
  simp only [CollatzResearch.WordTrace]
  refine ⟨52473772833832102162123633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69965030445109469549498177 52473772833832102162123633)
  ·
    refine ⟨39355329625374076621592725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52473772833832102162123633 39355329625374076621592725)
    ·
      refine ⟨1844781076189409841637159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39355329625374076621592725 1844781076189409841637159)
      ·
        refine ⟨2767171614284114762455739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844781076189409841637159 2767171614284114762455739)
        ·
          refine ⟨4150757421426172143683609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767171614284114762455739 4150757421426172143683609)
          ·
            refine ⟨3113068066069629107762707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4150757421426172143683609 3113068066069629107762707)
            ·
              refine ⟨4669602099104443661644061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113068066069629107762707 4669602099104443661644061)
              ·
                refine ⟨1751100787164166373116523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4669602099104443661644061 1751100787164166373116523)
                ·
                  refine ⟨2626651180746249559674785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751100787164166373116523 2626651180746249559674785)
                  ·
                    refine ⟨1969988385559687169756089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2626651180746249559674785 1969988385559687169756089)
                    ·
                      refine ⟨1477491289169765377317067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969988385559687169756089 1477491289169765377317067)
                      ·
                        rfl

theorem cell23_2877404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2877404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877404 prefixEnd_2877404 := by exact prefixLift 2877404
  have htrace : WordTrace (prefixWord ++ tailWord_2877404) baseStart_2877404 baseEnd_2877404 := by
    simpa [prefixWord, tailWord_2877404, baseEnd_2877404] using wordTrace_append hprefix tailTrace_2877404
  have hstable : (prefixWord ++ tailWord_2877404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877404).length < 2 ^ (prefixWord ++ tailWord_2877404).sum := by decide
  have hdescent : baseEnd_2877404 < baseStart_2877404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877409 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_2877409 : Nat := 118140960795 + 2877409 * 2 ^ 59
def prefixEnd_2877409 : Nat := 4983230072969 + 3 ^ 40 * 2877409 * 2
def baseEnd_2877409 : Nat := 1477493856573037857754543

theorem tailTrace_2877409 : CollatzResearch.WordTrace tailWord_2877409 prefixEnd_2877409 1477493856573037857754543 := by
  unfold tailWord_2877409
  simp only [CollatzResearch.WordTrace]
  refine ⟨104947728032646090178179281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69965152021764060118786187 104947728032646090178179281)
  ·
    refine ⟨78710796024484567633634461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104947728032646090178179281 78710796024484567633634461)
    ·
      refine ⟨29516548509181712862612923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78710796024484567633634461 29516548509181712862612923)
      ·
        refine ⟨44274822763772569293919385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29516548509181712862612923 44274822763772569293919385)
        ·
          refine ⟨33206117072829426970439539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44274822763772569293919385 33206117072829426970439539)
          ·
            refine ⟨49809175609244140455659309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33206117072829426970439539 49809175609244140455659309)
            ·
              refine ⟨18678440853466552670872241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49809175609244140455659309 18678440853466552670872241)
              ·
                refine ⟨14008830640099914503154181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18678440853466552670872241 14008830640099914503154181)
                ·
                  refine ⟨2626655745018733969341409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14008830640099914503154181 2626655745018733969341409)
                  ·
                    refine ⟨1969991808764050477006057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2626655745018733969341409 1969991808764050477006057)
                    ·
                      refine ⟨1477493856573037857754543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1969991808764050477006057 1477493856573037857754543)
                      ·
                        rfl

theorem cell23_2877409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_2877409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877409 prefixEnd_2877409 := by exact prefixLift 2877409
  have htrace : WordTrace (prefixWord ++ tailWord_2877409) baseStart_2877409 baseEnd_2877409 := by
    simpa [prefixWord, tailWord_2877409, baseEnd_2877409] using wordTrace_append hprefix tailTrace_2877409
  have hstable : (prefixWord ++ tailWord_2877409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877409).length < 2 ^ (prefixWord ++ tailWord_2877409).sum := by decide
  have hdescent : baseEnd_2877409 < baseStart_2877409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877432 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 5]
def baseStart_2877432 : Nat := 118140960795 + 2877432 * 2 ^ 59
def prefixEnd_2877432 : Nat := 4983230072969 + 3 ^ 40 * 2877432 * 2
def baseEnd_2877432 : Nat := 164167296292010140862993

theorem tailTrace_2877432 : CollatzResearch.WordTrace tailWord_2877432 prefixEnd_2877432 164167296292010140862993 := by
  unfold tailWord_2877432
  simp only [CollatzResearch.WordTrace]
  refine ⟨52474283455781382553133275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69965711274375176737511033 52474283455781382553133275)
  ·
    refine ⟨78711425183672073829699913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52474283455781382553133275 78711425183672073829699913)
    ·
      refine ⟨59033568887754055372274935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78711425183672073829699913 59033568887754055372274935)
      ·
        refine ⟨88550353331631083058412403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59033568887754055372274935 88550353331631083058412403)
        ·
          refine ⟨132825529997446624587618605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88550353331631083058412403 132825529997446624587618605)
          ·
            refine ⟨49809573749042484220356977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132825529997446624587618605 49809573749042484220356977)
            ·
              refine ⟨37357180311781863165267733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49809573749042484220356977 37357180311781863165267733)
              ·
                refine ⟨1751117827114774835871925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37357180311781863165267733 1751117827114774835871925)
                ·
                  refine ⟨164167296292010140862993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751117827114774835871925 164167296292010140862993)
                  ·
                    rfl

theorem cell23_2877432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 5].length) (baseStart_2877432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877432 prefixEnd_2877432 := by exact prefixLift 2877432
  have htrace : WordTrace (prefixWord ++ tailWord_2877432) baseStart_2877432 baseEnd_2877432 := by
    simpa [prefixWord, tailWord_2877432, baseEnd_2877432] using wordTrace_append hprefix tailTrace_2877432
  have hstable : (prefixWord ++ tailWord_2877432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877432).length < 2 ^ (prefixWord ++ tailWord_2877432).sum := by decide
  have hdescent : baseEnd_2877432 < baseStart_2877432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877559 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_2877559 : Nat := 118140960795 + 2877559 * 2 ^ 59
def prefixEnd_2877559 : Nat := 4983230072969 + 3 ^ 40 * 2877559 * 2
def baseEnd_2877559 : Nat := 1477570878671212270878853

theorem tailTrace_2877559 : CollatzResearch.WordTrace tailWord_2877559 prefixEnd_2877559 1477570878671212270878853 := by
  unfold tailWord_2877559
  simp only [CollatzResearch.WordTrace]
  refine ⟨104953198982102665796139731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69968799321401777197426487 104953198982102665796139731)
  ·
    refine ⟨157429798473153998694209597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104953198982102665796139731 157429798473153998694209597)
    ·
      refine ⟨59036174427432749510328599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157429798473153998694209597 59036174427432749510328599)
      ·
        refine ⟨88554261641149124265492899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59036174427432749510328599 88554261641149124265492899)
        ·
          refine ⟨132831392461723686398239349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88554261641149124265492899 132831392461723686398239349)
          ·
            refine ⟨12452943043286595599834939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132831392461723686398239349 12452943043286595599834939)
            ·
              refine ⟨18679414564929893399752409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12452943043286595599834939 18679414564929893399752409)
              ·
                refine ⟨14009560923697420049814307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18679414564929893399752409 14009560923697420049814307)
                ·
                  refine ⟨21014341385546130074721461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14009560923697420049814307 21014341385546130074721461)
                  ·
                    refine ⟨1970094504894949694505137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21014341385546130074721461 1970094504894949694505137)
                    ·
                      refine ⟨1477570878671212270878853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970094504894949694505137 1477570878671212270878853)
                      ·
                        rfl

theorem cell23_2877559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_2877559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877559 prefixEnd_2877559 := by exact prefixLift 2877559
  have htrace : WordTrace (prefixWord ++ tailWord_2877559) baseStart_2877559 baseEnd_2877559 := by
    simpa [prefixWord, tailWord_2877559, baseEnd_2877559] using wordTrace_append hprefix tailTrace_2877559
  have hstable : (prefixWord ++ tailWord_2877559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877559).length < 2 ^ (prefixWord ++ tailWord_2877559).sum := by decide
  have hdescent : baseEnd_2877559 < baseStart_2877559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877576 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2877576 : Nat := 118140960795 + 2877576 * 2 ^ 59
def prefixEnd_2877576 : Nat := 4983230072969 + 3 ^ 40 * 2877576 * 2
def baseEnd_2877576 : Nat := 1477579607842338704366275

theorem tailTrace_2877576 : CollatzResearch.WordTrace tailWord_2877576 prefixEnd_2877576 1477579607842338704366275 := by
  unfold tailWord_2877576
  simp only [CollatzResearch.WordTrace]
  refine ⟨52476909511520538849754291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69969212682027385133005721 52476909511520538849754291)
  ·
    refine ⟨78715364267280808274631437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52476909511520538849754291 78715364267280808274631437)
    ·
      refine ⟨29518261600230303102986789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78715364267280808274631437 29518261600230303102986789)
      ·
        refine ⟨5534674050043181831810023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29518261600230303102986789 5534674050043181831810023)
        ·
          refine ⟨8302011075064772747715035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534674050043181831810023 8302011075064772747715035)
          ·
            refine ⟨12453016612597159121572553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302011075064772747715035 12453016612597159121572553)
            ·
              refine ⟨9339762459447869341179415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12453016612597159121572553 9339762459447869341179415)
              ·
                refine ⟨14009643689171804011769123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9339762459447869341179415 14009643689171804011769123)
                ·
                  refine ⟨21014465533757706017653685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14009643689171804011769123 21014465533757706017653685)
                  ·
                    refine ⟨1970106143789784939155033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21014465533757706017653685 1970106143789784939155033)
                    ·
                      refine ⟨1477579607842338704366275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970106143789784939155033 1477579607842338704366275)
                      ·
                        rfl

theorem cell23_2877576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2877576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877576 prefixEnd_2877576 := by exact prefixLift 2877576
  have htrace : WordTrace (prefixWord ++ tailWord_2877576) baseStart_2877576 baseEnd_2877576 := by
    simpa [prefixWord, tailWord_2877576, baseEnd_2877576] using wordTrace_append hprefix tailTrace_2877576
  have hstable : (prefixWord ++ tailWord_2877576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877576).length < 2 ^ (prefixWord ++ tailWord_2877576).sum := by decide
  have hdescent : baseEnd_2877576 < baseStart_2877576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877589 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_2877589 : Nat := 118140960795 + 2877589 * 2 ^ 59
def prefixEnd_2877589 : Nat := 4983230072969 + 3 ^ 40 * 2877589 * 2
def baseEnd_2877589 : Nat := 1477586283090847153503715

theorem tailTrace_2877589 : CollatzResearch.WordTrace tailWord_2877589 prefixEnd_2877589 1477586283090847153503715 := by
  unfold tailWord_2877589
  simp only [CollatzResearch.WordTrace]
  refine ⟨104954293171993980919731821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69969528781329320613154547 104954293171993980919731821)
  ·
    refine ⟨39357859939497742844899433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104954293171993980919731821 39357859939497742844899433)
    ·
      refine ⟨29518394954623307133674575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39357859939497742844899433 29518394954623307133674575)
      ·
        refine ⟨44277592431934960700511863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29518394954623307133674575 44277592431934960700511863)
        ·
          refine ⟨66416388647902441050767795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44277592431934960700511863 66416388647902441050767795)
          ·
            refine ⟨99624582971853661576151693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66416388647902441050767795 99624582971853661576151693)
            ·
              refine ⟨37359218614445123091056885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99624582971853661576151693 37359218614445123091056885)
              ·
                refine ⟨3502426745104230289786583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37359218614445123091056885 3502426745104230289786583)
                ·
                  refine ⟨5253640117656345434679875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502426745104230289786583 5253640117656345434679875)
                  ·
                    refine ⟨7880460176484518152019813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5253640117656345434679875 7880460176484518152019813)
                    ·
                      refine ⟨1477586283090847153503715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7880460176484518152019813 1477586283090847153503715)
                      ·
                        rfl

theorem cell23_2877589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_2877589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877589 prefixEnd_2877589 := by exact prefixLift 2877589
  have htrace : WordTrace (prefixWord ++ tailWord_2877589) baseStart_2877589 baseEnd_2877589 := by
    simpa [prefixWord, tailWord_2877589, baseEnd_2877589] using wordTrace_append hprefix tailTrace_2877589
  have hstable : (prefixWord ++ tailWord_2877589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877589).length < 2 ^ (prefixWord ++ tailWord_2877589).sum := by decide
  have hdescent : baseEnd_2877589 < baseStart_2877589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877600 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 1, 1, 3]
def baseStart_2877600 : Nat := 118140960795 + 2877600 * 2 ^ 59
def prefixEnd_2877600 : Nat := 4983230072969 + 3 ^ 40 * 2877600 * 2
def baseEnd_2877600 : Nat := 1477591931378046610466165

theorem tailTrace_2877600 : CollatzResearch.WordTrace tailWord_2877600 prefixEnd_2877600 1477591931378046610466165 := by
  unfold tailWord_2877600
  simp only [CollatzResearch.WordTrace]
  refine ⟨52477347187477064899191127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69969796249969419865588169 52477347187477064899191127)
  ·
    refine ⟨78716020781215597348786691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52477347187477064899191127 78716020781215597348786691)
    ·
      refine ⟨118074031171823396023180037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78716020781215597348786691 118074031171823396023180037)
      ·
        refine ⟨22138880844716886754346257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118074031171823396023180037 22138880844716886754346257)
        ·
          refine ⟨16604160633537665065759693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22138880844716886754346257 16604160633537665065759693)
          ·
            refine ⟨6226560237576624399659885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16604160633537665065759693 6226560237576624399659885)
            ·
              refine ⟨2334960089091234149872457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6226560237576624399659885 2334960089091234149872457)
              ·
                refine ⟨1751220066818425612404343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334960089091234149872457 1751220066818425612404343)
                ·
                  refine ⟨2626830100227638418606515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751220066818425612404343 2626830100227638418606515)
                  ·
                    refine ⟨3940245150341457627909773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2626830100227638418606515 3940245150341457627909773)
                    ·
                      refine ⟨1477591931378046610466165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3940245150341457627909773 1477591931378046610466165)
                      ·
                        rfl

theorem cell23_2877600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_2877600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877600 prefixEnd_2877600 := by exact prefixLift 2877600
  have htrace : WordTrace (prefixWord ++ tailWord_2877600) baseStart_2877600 baseEnd_2877600 := by
    simpa [prefixWord, tailWord_2877600, baseEnd_2877600] using wordTrace_append hprefix tailTrace_2877600
  have hstable : (prefixWord ++ tailWord_2877600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877600).length < 2 ^ (prefixWord ++ tailWord_2877600).sum := by decide
  have hdescent : baseEnd_2877600 < baseStart_2877600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877620 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2877620 : Nat := 118140960795 + 2877620 * 2 ^ 59
def prefixEnd_2877620 : Nat := 4983230072969 + 3 ^ 40 * 2877620 * 2
def baseEnd_2877620 : Nat := 492534066997045510738691

theorem tailTrace_2877620 : CollatzResearch.WordTrace tailWord_2877620 prefixEnd_2877620 492534066997045510738691 := by
  unfold tailWord_2877620
  simp only [CollatzResearch.WordTrace]
  refine ⟨52477711917440836607055157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69970282556587782142740209 52477711917440836607055157)
  ·
    refine ⟨4919785492260078431911421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52477711917440836607055157 4919785492260078431911421)
    ·
      refine ⟨1844919559597529411966783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4919785492260078431911421 1844919559597529411966783)
      ·
        refine ⟨2767379339396294117950175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844919559597529411966783 2767379339396294117950175)
        ·
          refine ⟨4151069009094441176925263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767379339396294117950175 4151069009094441176925263)
          ·
            refine ⟨6226603513641661765387895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151069009094441176925263 6226603513641661765387895)
            ·
              refine ⟨9339905270462492648081843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226603513641661765387895 9339905270462492648081843)
              ·
                refine ⟨14009857905693738972122765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9339905270462492648081843 14009857905693738972122765)
                ·
                  refine ⟨5253696714635152114546037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14009857905693738972122765 5253696714635152114546037)
                  ·
                    refine ⟨492534066997045510738691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5253696714635152114546037 492534066997045510738691)
                    ·
                      rfl

theorem cell23_2877620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2877620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877620 prefixEnd_2877620 := by exact prefixLift 2877620
  have htrace : WordTrace (prefixWord ++ tailWord_2877620) baseStart_2877620 baseEnd_2877620 := by
    simpa [prefixWord, tailWord_2877620, baseEnd_2877620] using wordTrace_append hprefix tailTrace_2877620
  have hstable : (prefixWord ++ tailWord_2877620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877620).length < 2 ^ (prefixWord ++ tailWord_2877620).sum := by decide
  have hdescent : baseEnd_2877620 < baseStart_2877620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877626 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_2877626 : Nat := 118140960795 + 2877626 * 2 ^ 59
def prefixEnd_2877626 : Nat := 4983230072969 + 3 ^ 40 * 2877626 * 2
def baseEnd_2877626 : Nat := 1477605281875063508741045

theorem tailTrace_2877626 : CollatzResearch.WordTrace tailWord_2877626 prefixEnd_2877626 1477605281875063508741045 := by
  unfold tailWord_2877626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26238910668214984059707183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69970428448573290825885821 26238910668214984059707183)
  ·
    refine ⟨39358366002322476089560775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26238910668214984059707183 39358366002322476089560775)
    ·
      refine ⟨59037549003483714134341163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39358366002322476089560775 59037549003483714134341163)
      ·
        refine ⟨88556323505225571201511745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59037549003483714134341163 88556323505225571201511745)
        ·
          refine ⟨66417242628919178401133809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88556323505225571201511745 66417242628919178401133809)
          ·
            refine ⟨49812931971689383800850357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66417242628919178401133809 49812931971689383800850357)
            ·
              refine ⟨4669962372345879731329721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49812931971689383800850357 4669962372345879731329721)
              ·
                refine ⟨3502471779259409798497291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669962372345879731329721 3502471779259409798497291)
                ·
                  refine ⟨5253707668889114697745937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502471779259409798497291 5253707668889114697745937)
                  ·
                    refine ⟨3940280751666836023309453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5253707668889114697745937 3940280751666836023309453)
                    ·
                      refine ⟨1477605281875063508741045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3940280751666836023309453 1477605281875063508741045)
                      ·
                        rfl

theorem cell23_2877626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_2877626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877626 prefixEnd_2877626 := by exact prefixLift 2877626
  have htrace : WordTrace (prefixWord ++ tailWord_2877626) baseStart_2877626 baseEnd_2877626 := by
    simpa [prefixWord, tailWord_2877626, baseEnd_2877626] using wordTrace_append hprefix tailTrace_2877626
  have hstable : (prefixWord ++ tailWord_2877626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877626).length < 2 ^ (prefixWord ++ tailWord_2877626).sum := by decide
  have hdescent : baseEnd_2877626 < baseStart_2877626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877636 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2877636 : Nat := 118140960795 + 2877636 * 2 ^ 59
def prefixEnd_2877636 : Nat := 4983230072969 + 3 ^ 40 * 2877636 * 2
def baseEnd_2877636 : Nat := 1477610416681608469615999

theorem tailTrace_2877636 : CollatzResearch.WordTrace tailWord_2877636 prefixEnd_2877636 1477610416681608469615999 := by
  unfold tailWord_2877636
  simp only [CollatzResearch.WordTrace]
  refine ⟨52478003701411853973346381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69970671601882471964461841 52478003701411853973346381)
  ·
    refine ⟨19679251388029445240004893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52478003701411853973346381 19679251388029445240004893)
    ·
      refine ⟨7379719270511041965001835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19679251388029445240004893 7379719270511041965001835)
      ·
        refine ⟨11069578905766562947502753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379719270511041965001835 11069578905766562947502753)
        ·
          refine ⟨8302184179324922210627065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11069578905766562947502753 8302184179324922210627065)
          ·
            refine ⟨6226638134493691657970299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8302184179324922210627065 6226638134493691657970299)
            ·
              refine ⟨9339957201740537486955449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226638134493691657970299 9339957201740537486955449)
              ·
                refine ⟨7004967901305403115216587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9339957201740537486955449 7004967901305403115216587)
                ·
                  refine ⟨10507451851958104672824881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004967901305403115216587 10507451851958104672824881)
                  ·
                    refine ⟨7880588888968578504618661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10507451851958104672824881 7880588888968578504618661)
                    ·
                      refine ⟨1477610416681608469615999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7880588888968578504618661 1477610416681608469615999)
                      ·
                        rfl

theorem cell23_2877636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2877636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877636 prefixEnd_2877636 := by exact prefixLift 2877636
  have htrace : WordTrace (prefixWord ++ tailWord_2877636) baseStart_2877636 baseEnd_2877636 := by
    simpa [prefixWord, tailWord_2877636, baseEnd_2877636] using wordTrace_append hprefix tailTrace_2877636
  have hstable : (prefixWord ++ tailWord_2877636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877636).length < 2 ^ (prefixWord ++ tailWord_2877636).sum := by decide
  have hdescent : baseEnd_2877636 < baseStart_2877636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877696 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2]
def baseStart_2877696 : Nat := 118140960795 + 2877696 * 2 ^ 59
def prefixEnd_2877696 : Nat := 4983230072969 + 3 ^ 40 * 2877696 * 2
def baseEnd_2877696 : Nat := 1477641225520878234865723

theorem tailTrace_2877696 : CollatzResearch.WordTrace tailWord_2877696 prefixEnd_2877696 1477641225520878234865723 := by
  unfold tailWord_2877696
  simp only [CollatzResearch.WordTrace]
  refine ⟨52479097891303169096938471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69972130521737558795917961 52479097891303169096938471)
  ·
    refine ⟨78718646836954753645407707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52479097891303169096938471 78718646836954753645407707)
    ·
      refine ⟨118077970255432130468111561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78718646836954753645407707 118077970255432130468111561)
      ·
        refine ⟨88558477691574097851083671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118077970255432130468111561 88558477691574097851083671)
        ·
          refine ⟨132837716537361146776625507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88558477691574097851083671 132837716537361146776625507)
          ·
            refine ⟨199256574806041720164938261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132837716537361146776625507 199256574806041720164938261)
            ·
              refine ⟨9340151944033205632731481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 199256574806041720164938261 9340151944033205632731481)
              ·
                refine ⟨7005113958024904224548611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9340151944033205632731481 7005113958024904224548611)
                ·
                  refine ⟨10507670937037356336822917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005113958024904224548611 10507670937037356336822917)
                  ·
                    refine ⟨1970188300694504313154297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10507670937037356336822917 1970188300694504313154297)
                    ·
                      refine ⟨1477641225520878234865723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970188300694504313154297 1477641225520878234865723)
                      ·
                        rfl

theorem cell23_2877696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_2877696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877696 prefixEnd_2877696 := by exact prefixLift 2877696
  have htrace : WordTrace (prefixWord ++ tailWord_2877696) baseStart_2877696 baseEnd_2877696 := by
    simpa [prefixWord, tailWord_2877696, baseEnd_2877696] using wordTrace_append hprefix tailTrace_2877696
  have hstable : (prefixWord ++ tailWord_2877696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877696).length < 2 ^ (prefixWord ++ tailWord_2877696).sum := by decide
  have hdescent : baseEnd_2877696 < baseStart_2877696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877700 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2877700 : Nat := 118140960795 + 2877700 * 2 ^ 59
def prefixEnd_2877700 : Nat := 4983230072969 + 3 ^ 40 * 2877700 * 2
def baseEnd_2877700 : Nat := 1477643279443496219215705

theorem tailTrace_2877700 : CollatzResearch.WordTrace tailWord_2877700 prefixEnd_2877700 1477643279443496219215705 := by
  unfold tailWord_2877700
  simp only [CollatzResearch.WordTrace]
  refine ⟨52479170837295923438511277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69972227783061231251348369 52479170837295923438511277)
  ·
    refine ⟨19679689063985971289441729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52479170837295923438511277 19679689063985971289441729)
    ·
      refine ⟨14759766797989478467081297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19679689063985971289441729 14759766797989478467081297)
      ·
        refine ⟨11069825098492108850310973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14759766797989478467081297 11069825098492108850310973)
        ·
          refine ⟨4151184411934540818866615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11069825098492108850310973 4151184411934540818866615)
          ·
            refine ⟨6226776617901811228299923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151184411934540818866615 6226776617901811228299923)
            ·
              refine ⟨9340164926852716842449885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226776617901811228299923 9340164926852716842449885)
              ·
                refine ⟨3502561847569768815918707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9340164926852716842449885 3502561847569768815918707)
                ·
                  refine ⟨5253842771354653223878061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502561847569768815918707 5253842771354653223878061)
                  ·
                    refine ⟨1970191039257994958954273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5253842771354653223878061 1970191039257994958954273)
                    ·
                      refine ⟨1477643279443496219215705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970191039257994958954273 1477643279443496219215705)
                      ·
                        rfl

theorem cell23_2877700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2877700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877700 prefixEnd_2877700 := by exact prefixLift 2877700
  have htrace : WordTrace (prefixWord ++ tailWord_2877700) baseStart_2877700 baseEnd_2877700 := by
    simpa [prefixWord, tailWord_2877700, baseEnd_2877700] using wordTrace_append hprefix tailTrace_2877700
  have hstable : (prefixWord ++ tailWord_2877700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877700).length < 2 ^ (prefixWord ++ tailWord_2877700).sum := by decide
  have hdescent : baseEnd_2877700 < baseStart_2877700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877713 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_2877713 : Nat := 118140960795 + 2877713 * 2 ^ 59
def prefixEnd_2877713 : Nat := 4983230072969 + 3 ^ 40 * 2877713 * 2
def baseEnd_2877713 : Nat := 1477649954692004668353145

theorem tailTrace_2877713 : CollatzResearch.WordTrace tailWord_2877713 prefixEnd_2877713 1477649954692004668353145 := by
  unfold tailWord_2877713
  simp only [CollatzResearch.WordTrace]
  refine ⟨104958815823544750097245793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69972543882363166731497195 104958815823544750097245793)
  ·
    refine ⟨78719111867658562572934345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104958815823544750097245793 78719111867658562572934345)
    ·
      refine ⟨59039333900743921929700759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78719111867658562572934345 59039333900743921929700759)
      ·
        refine ⟨88559000851115882894551139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59039333900743921929700759 88559000851115882894551139)
        ·
          refine ⟨132838501276673824341826709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88559000851115882894551139 132838501276673824341826709)
          ·
            refine ⟨6226804747344085516023127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132838501276673824341826709 6226804747344085516023127)
            ·
              refine ⟨9340207121016128274034691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226804747344085516023127 9340207121016128274034691)
              ·
                refine ⟨14010310681524192411052037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9340207121016128274034691 14010310681524192411052037)
                ·
                  refine ⟨2626933252785786077072257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14010310681524192411052037 2626933252785786077072257)
                  ·
                    refine ⟨1970199939589339557804193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2626933252785786077072257 1970199939589339557804193)
                    ·
                      refine ⟨1477649954692004668353145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970199939589339557804193 1477649954692004668353145)
                      ·
                        rfl

theorem cell23_2877713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_2877713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877713 prefixEnd_2877713 := by exact prefixLift 2877713
  have htrace : WordTrace (prefixWord ++ tailWord_2877713) baseStart_2877713 baseEnd_2877713 := by
    simpa [prefixWord, tailWord_2877713, baseEnd_2877713] using wordTrace_append hprefix tailTrace_2877713
  have hstable : (prefixWord ++ tailWord_2877713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877713).length < 2 ^ (prefixWord ++ tailWord_2877713).sum := by decide
  have hdescent : baseEnd_2877713 < baseStart_2877713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877719 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 7]
def baseStart_2877719 : Nat := 118140960795 + 2877719 * 2 ^ 59
def prefixEnd_2877719 : Nat := 4983230072969 + 3 ^ 40 * 2877719 * 2
def baseEnd_2877719 : Nat := 164183670619547960542013

theorem tailTrace_2877719 : CollatzResearch.WordTrace tailWord_2877719 prefixEnd_2877719 164183670619547960542013 := by
  unfold tailWord_2877719
  simp only [CollatzResearch.WordTrace]
  refine ⟨104959034661523013121964211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69972689774348675414642807 104959034661523013121964211)
  ·
    refine ⟨157438551992284519682946317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104959034661523013121964211 157438551992284519682946317)
    ·
      refine ⟨59039456997106694881104869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157438551992284519682946317 59039456997106694881104869)
      ·
        refine ⟨11069898186957505290207163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59039456997106694881104869 11069898186957505290207163)
        ·
          refine ⟨16604847280436257935310745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11069898186957505290207163 16604847280436257935310745)
          ·
            refine ⟨12453635460327193451483059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16604847280436257935310745 12453635460327193451483059)
            ·
              refine ⟨18680453190490790177224589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12453635460327193451483059 18680453190490790177224589)
              ·
                refine ⟨7005169946434046316459221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18680453190490790177224589 7005169946434046316459221)
                ·
                  refine ⟨164183670619547960542013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7005169946434046316459221 164183670619547960542013)
                  ·
                    rfl

theorem cell23_2877719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 7].length) (baseStart_2877719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877719 prefixEnd_2877719 := by exact prefixLift 2877719
  have htrace : WordTrace (prefixWord ++ tailWord_2877719) baseStart_2877719 baseEnd_2877719 := by
    simpa [prefixWord, tailWord_2877719, baseEnd_2877719] using wordTrace_append hprefix tailTrace_2877719
  have hstable : (prefixWord ++ tailWord_2877719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877719).length < 2 ^ (prefixWord ++ tailWord_2877719).sum := by decide
  have hdescent : baseEnd_2877719 < baseStart_2877719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877730 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_2877730 : Nat := 118140960795 + 2877730 * 2 ^ 59
def prefixEnd_2877730 : Nat := 4983230072969 + 3 ^ 40 * 2877730 * 2
def baseEnd_2877730 : Nat := 1477658683863131101840567

theorem tailTrace_2877730 : CollatzResearch.WordTrace tailWord_2877730 prefixEnd_2877730 1477658683863131101840567 := by
  unfold tailWord_2877730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239858966120790500153661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69972957242988774667076429 26239858966120790500153661)
  ·
    refine ⟨9839947112295296437557623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26239858966120790500153661 9839947112295296437557623)
    ·
      refine ⟨14759920668442944656336435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9839947112295296437557623 14759920668442944656336435)
      ·
        refine ⟨22139881002664416984504653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14759920668442944656336435 22139881002664416984504653)
        ·
          refine ⟨8302455375999156369189245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22139881002664416984504653 8302455375999156369189245)
          ·
            refine ⟨3113420765999683638445967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8302455375999156369189245 3113420765999683638445967)
            ·
              refine ⟨4670131148999525457668951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113420765999683638445967 4670131148999525457668951)
              ·
                refine ⟨7005196723499288186503427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670131148999525457668951 7005196723499288186503427)
                ·
                  refine ⟨10507795085248932279755141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005196723499288186503427 10507795085248932279755141)
                  ·
                    refine ⟨1970211578484174802454089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10507795085248932279755141 1970211578484174802454089)
                    ·
                      refine ⟨1477658683863131101840567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970211578484174802454089 1477658683863131101840567)
                      ·
                        rfl

theorem cell23_2877730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_2877730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877730 prefixEnd_2877730 := by exact prefixLift 2877730
  have htrace : WordTrace (prefixWord ++ tailWord_2877730) baseStart_2877730 baseEnd_2877730 := by
    simpa [prefixWord, tailWord_2877730, baseEnd_2877730] using wordTrace_append hprefix tailTrace_2877730
  have hstable : (prefixWord ++ tailWord_2877730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877730).length < 2 ^ (prefixWord ++ tailWord_2877730).sum := by decide
  have hdescent : baseEnd_2877730 < baseStart_2877730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877749 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2877749 : Nat := 118140960795 + 2877749 * 2 ^ 59
def prefixEnd_2877749 : Nat := 4983230072969 + 3 ^ 40 * 2877749 * 2
def baseEnd_2877749 : Nat := 492556146665188842500993

theorem tailTrace_2877749 : CollatzResearch.WordTrace tailWord_2877749 prefixEnd_2877749 492556146665188842500993 := by
  unfold tailWord_2877749
  simp only [CollatzResearch.WordTrace]
  refine ⟨104960128851414328245556301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69973419234276218830370867 104960128851414328245556301)
  ·
    refine ⟨39360048319280373092083613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104960128851414328245556301 39360048319280373092083613)
    ·
      refine ⟨14760018119730139909531355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39360048319280373092083613 14760018119730139909531355)
      ·
        refine ⟨22140027179595209864297033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760018119730139909531355 22140027179595209864297033)
        ·
          refine ⟨16605020384696407398222775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22140027179595209864297033 16605020384696407398222775)
          ·
            refine ⟨24907530577044611097334163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16605020384696407398222775 24907530577044611097334163)
            ·
              refine ⟨37361295865566916646001245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24907530577044611097334163 37361295865566916646001245)
              ·
                refine ⟨14010485949587593742250467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37361295865566916646001245 14010485949587593742250467)
                ·
                  refine ⟨21015728924381390613375701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14010485949587593742250467 21015728924381390613375701)
                  ·
                    refine ⟨492556146665188842500993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21015728924381390613375701 492556146665188842500993)
                    ·
                      rfl

theorem cell23_2877749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2877749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877749 prefixEnd_2877749 := by exact prefixLift 2877749
  have htrace : WordTrace (prefixWord ++ tailWord_2877749) baseStart_2877749 baseEnd_2877749 := by
    simpa [prefixWord, tailWord_2877749, baseEnd_2877749] using wordTrace_append hprefix tailTrace_2877749
  have hstable : (prefixWord ++ tailWord_2877749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877749).length < 2 ^ (prefixWord ++ tailWord_2877749).sum := by decide
  have hdescent : baseEnd_2877749 < baseStart_2877749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877753 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 5]
def baseStart_2877753 : Nat := 118140960795 + 2877753 * 2 ^ 59
def prefixEnd_2877753 : Nat := 4983230072969 + 3 ^ 40 * 2877753 * 2
def baseEnd_2877753 : Nat := 164185610435353834650329

theorem tailTrace_2877753 : CollatzResearch.WordTrace tailWord_2877753 prefixEnd_2877753 164185610435353834650329 := by
  unfold tailWord_2877753
  simp only [CollatzResearch.WordTrace]
  refine ⟨104960274743399836928701913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69973516495599891285801275 104960274743399836928701913)
  ·
    refine ⟨78720206057549877696526435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104960274743399836928701913 78720206057549877696526435)
    ·
      refine ⟨118080309086324816544789653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78720206057549877696526435 118080309086324816544789653)
      ·
        refine ⟨5535014488421475775537015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118080309086324816544789653 5535014488421475775537015)
        ·
          refine ⟨8302521732632213663305523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535014488421475775537015 8302521732632213663305523)
          ·
            refine ⟨12453782598948320494958285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302521732632213663305523 12453782598948320494958285)
            ·
              refine ⟨4670168474605620185609357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12453782598948320494958285 4670168474605620185609357)
              ·
                refine ⟨1751313177977107569603509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4670168474605620185609357 1751313177977107569603509)
                ·
                  refine ⟨164185610435353834650329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751313177977107569603509 164185610435353834650329)
                  ·
                    rfl

theorem cell23_2877753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 5].length) (baseStart_2877753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877753 prefixEnd_2877753 := by exact prefixLift 2877753
  have htrace : WordTrace (prefixWord ++ tailWord_2877753) baseStart_2877753 baseEnd_2877753 := by
    simpa [prefixWord, tailWord_2877753, baseEnd_2877753] using wordTrace_append hprefix tailTrace_2877753
  have hstable : (prefixWord ++ tailWord_2877753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877753).length < 2 ^ (prefixWord ++ tailWord_2877753).sum := by decide
  have hdescent : baseEnd_2877753 < baseStart_2877753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877759 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_2877759 : Nat := 118140960795 + 2877759 * 2 ^ 59
def prefixEnd_2877759 : Nat := 4983230072969 + 3 ^ 40 * 2877759 * 2
def baseEnd_2877759 : Nat := 1477673574802111488377933

theorem tailTrace_2877759 : CollatzResearch.WordTrace tailWord_2877759 prefixEnd_2877759 1477673574802111488377933 := by
  unfold tailWord_2877759
  simp only [CollatzResearch.WordTrace]
  refine ⟨104960493581378099953420331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69973662387585399968946887 104960493581378099953420331)
  ·
    refine ⟨157440740372067149930130497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104960493581378099953420331 157440740372067149930130497)
    ·
      refine ⟨118080555279050362447597873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157440740372067149930130497 118080555279050362447597873)
      ·
        refine ⟨88560416459287771835698405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118080555279050362447597873 88560416459287771835698405)
        ·
          refine ⟨16605078086116457219193451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88560416459287771835698405 16605078086116457219193451)
          ·
            refine ⟨24907617129174685828790177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16605078086116457219193451 24907617129174685828790177)
            ·
              refine ⟨18680712846881014371592633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24907617129174685828790177 18680712846881014371592633)
              ·
                refine ⟨14010534635160760778694475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18680712846881014371592633 14010534635160760778694475)
                ·
                  refine ⟨21015801952741141168041713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14010534635160760778694475 21015801952741141168041713)
                  ·
                    refine ⟨15761851464555855876031285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21015801952741141168041713 15761851464555855876031285)
                    ·
                      refine ⟨1477673574802111488377933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15761851464555855876031285 1477673574802111488377933)
                      ·
                        rfl

theorem cell23_2877759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_2877759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877759 prefixEnd_2877759 := by exact prefixLift 2877759
  have htrace : WordTrace (prefixWord ++ tailWord_2877759) baseStart_2877759 baseEnd_2877759 := by
    simpa [prefixWord, tailWord_2877759, baseEnd_2877759] using wordTrace_append hprefix tailTrace_2877759
  have hstable : (prefixWord ++ tailWord_2877759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877759).length < 2 ^ (prefixWord ++ tailWord_2877759).sum := by decide
  have hdescent : baseEnd_2877759 < baseStart_2877759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877786 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_2877786 : Nat := 118140960795 + 2877786 * 2 ^ 59
def prefixEnd_2877786 : Nat := 4983230072969 + 3 ^ 40 * 2877786 * 2
def baseEnd_2877786 : Nat := 1477687438779782882740309

theorem tailTrace_2877786 : CollatzResearch.WordTrace tailWord_2877786 prefixEnd_2877786 1477687438779782882740309 := by
  unfold tailWord_2877786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26240369588070070891163303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69974318901520189043102141 26240369588070070891163303)
  ·
    refine ⟨39360554382105106336744955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26240369588070070891163303 39360554382105106336744955)
    ·
      refine ⟨59040831573157659505117433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39360554382105106336744955 59040831573157659505117433)
      ·
        refine ⟨44280623679868244628838075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59040831573157659505117433 44280623679868244628838075)
        ·
          refine ⟨66420935519802366943257113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44280623679868244628838075 66420935519802366943257113)
          ·
            refine ⟨49815701639851775207442835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66420935519802366943257113 49815701639851775207442835)
            ·
              refine ⟨74723552459777662811164253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49815701639851775207442835 74723552459777662811164253)
              ·
                refine ⟨28021332172416623554186595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74723552459777662811164253 28021332172416623554186595)
                ·
                  refine ⟨42031998258624935331279893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28021332172416623554186595 42031998258624935331279893)
                  ·
                    refine ⟨1970249918373043843653745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42031998258624935331279893 1970249918373043843653745)
                    ·
                      refine ⟨1477687438779782882740309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970249918373043843653745 1477687438779782882740309)
                      ·
                        rfl

theorem cell23_2877786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_2877786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877786 prefixEnd_2877786 := by exact prefixLift 2877786
  have htrace : WordTrace (prefixWord ++ tailWord_2877786) baseStart_2877786 baseEnd_2877786 := by
    simpa [prefixWord, tailWord_2877786, baseEnd_2877786] using wordTrace_append hprefix tailTrace_2877786
  have hstable : (prefixWord ++ tailWord_2877786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877786).length < 2 ^ (prefixWord ++ tailWord_2877786).sum := by decide
  have hdescent : baseEnd_2877786 < baseStart_2877786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877796 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_2877796 : Nat := 118140960795 + 2877796 * 2 ^ 59
def prefixEnd_2877796 : Nat := 4983230072969 + 3 ^ 40 * 2877796 * 2
def baseEnd_2877796 : Nat := 492564191195442614538421

theorem tailTrace_2877796 : CollatzResearch.WordTrace tailWord_2877796 prefixEnd_2877796 492564191195442614538421 := by
  unfold tailWord_2877796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52480921541122027636258621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69974562054829370181678161 52480921541122027636258621)
  ·
    refine ⟨19680345577920760363596983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52480921541122027636258621 19680345577920760363596983)
    ·
      refine ⟨29520518366881140545395475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19680345577920760363596983 29520518366881140545395475)
      ·
        refine ⟨44280777550321710818093213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29520518366881140545395475 44280777550321710818093213)
        ·
          refine ⟨16605291581370641556784955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44280777550321710818093213 16605291581370641556784955)
          ·
            refine ⟨24907937372055962335177433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16605291581370641556784955 24907937372055962335177433)
            ·
              refine ⟨18680953029041971751383075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24907937372055962335177433 18680953029041971751383075)
              ·
                refine ⟨28021429543562957627074613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18680953029041971751383075 28021429543562957627074613)
                ·
                  refine ⟨2627009019709027277538245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28021429543562957627074613 2627009019709027277538245)
                  ·
                    refine ⟨492564191195442614538421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2627009019709027277538245 492564191195442614538421)
                    ·
                      rfl

theorem cell23_2877796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_2877796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877796 prefixEnd_2877796 := by exact prefixLift 2877796
  have htrace : WordTrace (prefixWord ++ tailWord_2877796) baseStart_2877796 baseEnd_2877796 := by
    simpa [prefixWord, tailWord_2877796, baseEnd_2877796] using wordTrace_append hprefix tailTrace_2877796
  have hstable : (prefixWord ++ tailWord_2877796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877796).length < 2 ^ (prefixWord ++ tailWord_2877796).sum := by decide
  have hdescent : baseEnd_2877796 < baseStart_2877796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877829 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2877829 : Nat := 118140960795 + 2877829 * 2 ^ 59
def prefixEnd_2877829 : Nat := 4983230072969 + 3 ^ 40 * 2877829 * 2
def baseEnd_2877829 : Nat := 1477709518447926214502611

theorem tailTrace_2877829 : CollatzResearch.WordTrace tailWord_2877829 prefixEnd_2877829 1477709518447926214502611 := by
  unfold tailWord_2877829
  simp only [CollatzResearch.WordTrace]
  refine ⟨104963046691124501908468541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69975364460749667938979027 104963046691124501908468541)
  ·
    refine ⟨39361142509171688215675703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104963046691124501908468541 39361142509171688215675703)
    ·
      refine ⟨59041713763757532323513555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39361142509171688215675703 59041713763757532323513555)
      ·
        refine ⟨88562570645636298485270333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59041713763757532323513555 88562570645636298485270333)
        ·
          refine ⟨33210963992113611931976375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88562570645636298485270333 33210963992113611931976375)
          ·
            refine ⟨49816445988170417897964563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33210963992113611931976375 49816445988170417897964563)
            ·
              refine ⟨74724668982255626846946845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49816445988170417897964563 74724668982255626846946845)
              ·
                refine ⟨28021750868345860067605067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74724668982255626846946845 28021750868345860067605067)
                ·
                  refine ⟨42032626302518790101407601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28021750868345860067605067 42032626302518790101407601)
                  ·
                    refine ⟨31524469726889092576055701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42032626302518790101407601 31524469726889092576055701)
                    ·
                      refine ⟨1477709518447926214502611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31524469726889092576055701 1477709518447926214502611)
                      ·
                        rfl

theorem cell23_2877829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2877829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877829 prefixEnd_2877829 := by exact prefixLift 2877829
  have htrace : WordTrace (prefixWord ++ tailWord_2877829) baseStart_2877829 baseEnd_2877829 := by
    simpa [prefixWord, tailWord_2877829, baseEnd_2877829] using wordTrace_append hprefix tailTrace_2877829
  have hstable : (prefixWord ++ tailWord_2877829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877829).length < 2 ^ (prefixWord ++ tailWord_2877829).sum := by decide
  have hdescent : baseEnd_2877829 < baseStart_2877829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877849 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2877849 : Nat := 118140960795 + 2877849 * 2 ^ 59
def prefixEnd_2877849 : Nat := 4983230072969 + 3 ^ 40 * 2877849 * 2
def baseEnd_2877849 : Nat := 1477719788061016136252519

theorem tailTrace_2877849 : CollatzResearch.WordTrace tailWord_2877849 prefixEnd_2877849 1477719788061016136252519 := by
  unfold tailWord_2877849
  simp only [CollatzResearch.WordTrace]
  refine ⟨104963776151052045324196601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69975850767368030216131067 104963776151052045324196601)
  ·
    refine ⟨78722832113289033993147451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104963776151052045324196601 78722832113289033993147451)
    ·
      refine ⟨118084248169933550989721177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78722832113289033993147451 118084248169933550989721177)
      ·
        refine ⟨88563186127450163242290883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118084248169933550989721177 88563186127450163242290883)
        ·
          refine ⟨132844779191175244863436325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88563186127450163242290883 132844779191175244863436325)
          ·
            refine ⟨24908396098345358411894311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132844779191175244863436325 24908396098345358411894311)
            ·
              refine ⟨37362594147518037617841467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24908396098345358411894311 37362594147518037617841467)
              ·
                refine ⟨56043891221277056426762201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37362594147518037617841467 56043891221277056426762201)
                ·
                  refine ⟨42032918415957792320071651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56043891221277056426762201 42032918415957792320071651)
                  ·
                    refine ⟨63049377623936688480107477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42032918415957792320071651 63049377623936688480107477)
                    ·
                      refine ⟨1477719788061016136252519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63049377623936688480107477 1477719788061016136252519)
                      ·
                        rfl

theorem cell23_2877849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2877849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877849 prefixEnd_2877849 := by exact prefixLift 2877849
  have htrace : WordTrace (prefixWord ++ tailWord_2877849) baseStart_2877849 baseEnd_2877849 := by
    simpa [prefixWord, tailWord_2877849, baseEnd_2877849] using wordTrace_append hprefix tailTrace_2877849
  have hstable : (prefixWord ++ tailWord_2877849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877849).length < 2 ^ (prefixWord ++ tailWord_2877849).sum := by decide
  have hdescent : baseEnd_2877849 < baseStart_2877849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877856 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_2877856 : Nat := 118140960795 + 2877856 * 2 ^ 59
def prefixEnd_2877856 : Nat := 4983230072969 + 3 ^ 40 * 2877856 * 2
def baseEnd_2877856 : Nat := 492574460808532536288329

theorem tailTrace_2877856 : CollatzResearch.WordTrace tailWord_2877856 prefixEnd_2877856 492574460808532536288329 := by
  unfold tailWord_2877856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52482015731013342759850711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69976020974684457013134281 52482015731013342759850711)
  ·
    refine ⟨78723023596520014139776067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52482015731013342759850711 78723023596520014139776067)
    ·
      refine ⟨118084535394780021209664101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78723023596520014139776067 118084535394780021209664101)
      ·
        refine ⟨22140850386521253976812019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118084535394780021209664101 22140850386521253976812019)
        ·
          refine ⟨33211275579781880965218029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22140850386521253976812019 33211275579781880965218029)
          ·
            refine ⟨12454228342418205361956761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33211275579781880965218029 12454228342418205361956761)
            ·
              refine ⟨9340671256813654021467571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12454228342418205361956761 9340671256813654021467571)
              ·
                refine ⟨14011006885220481032201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9340671256813654021467571 14011006885220481032201357)
                ·
                  refine ⟨5254127581957680387075509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14011006885220481032201357 5254127581957680387075509)
                  ·
                    refine ⟨492574460808532536288329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5254127581957680387075509 492574460808532536288329)
                    ·
                      rfl

theorem cell23_2877856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_2877856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877856 prefixEnd_2877856 := by exact prefixLift 2877856
  have htrace : WordTrace (prefixWord ++ tailWord_2877856) baseStart_2877856 baseEnd_2877856 := by
    simpa [prefixWord, tailWord_2877856, baseEnd_2877856] using wordTrace_append hprefix tailTrace_2877856
  have hstable : (prefixWord ++ tailWord_2877856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877856).length < 2 ^ (prefixWord ++ tailWord_2877856).sum := by decide
  have hdescent : baseEnd_2877856 < baseStart_2877856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877857 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2877857 : Nat := 118140960795 + 2877857 * 2 ^ 59
def prefixEnd_2877857 : Nat := 4983230072969 + 3 ^ 40 * 2877857 * 2
def baseEnd_2877857 : Nat := 1477723895906252104952483

theorem tailTrace_2877857 : CollatzResearch.WordTrace tailWord_2877857 prefixEnd_2877857 1477723895906252104952483 := by
  unfold tailWord_2877857
  simp only [CollatzResearch.WordTrace]
  refine ⟨104964067935023062690487825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69976045290015375126991883 104964067935023062690487825)
  ·
    refine ⟨78723050951267297017865869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104964067935023062690487825 78723050951267297017865869)
    ·
      refine ⟨29521144106725236381699701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78723050951267297017865869 29521144106725236381699701)
      ·
        refine ⟨2767607260005490910784347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29521144106725236381699701 2767607260005490910784347)
        ·
          refine ⟨4151410890008236366176521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767607260005490910784347 4151410890008236366176521)
          ·
            refine ⟨3113558167506177274632391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151410890008236366176521 3113558167506177274632391)
            ·
              refine ⟨4670337251259265911948587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113558167506177274632391 4670337251259265911948587)
              ·
                refine ⟨7005505876888898867922881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670337251259265911948587 7005505876888898867922881)
                ·
                  refine ⟨5254129407666674150942161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005505876888898867922881 5254129407666674150942161)
                  ·
                    refine ⟨3940597055750005613206621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5254129407666674150942161 3940597055750005613206621)
                    ·
                      refine ⟨1477723895906252104952483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3940597055750005613206621 1477723895906252104952483)
                      ·
                        rfl

theorem cell23_2877857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2877857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877857 prefixEnd_2877857 := by exact prefixLift 2877857
  have htrace : WordTrace (prefixWord ++ tailWord_2877857) baseStart_2877857 baseEnd_2877857 := by
    simpa [prefixWord, tailWord_2877857, baseEnd_2877857] using wordTrace_append hprefix tailTrace_2877857
  have hstable : (prefixWord ++ tailWord_2877857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877857).length < 2 ^ (prefixWord ++ tailWord_2877857).sum := by decide
  have hdescent : baseEnd_2877857 < baseStart_2877857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877873 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_2877873 : Nat := 118140960795 + 2877873 * 2 ^ 59
def prefixEnd_2877873 : Nat := 4983230072969 + 3 ^ 40 * 2877873 * 2
def baseEnd_2877873 : Nat := 492577370532241347450803

theorem tailTrace_2877873 : CollatzResearch.WordTrace tailWord_2877873 prefixEnd_2877873 492577370532241347450803 := by
  unfold tailWord_2877873
  simp only [CollatzResearch.WordTrace]
  refine ⟨104964651502965097423070273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69976434335310064948713515 104964651502965097423070273)
  ·
    refine ⟨78723488627223823067302705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104964651502965097423070273 78723488627223823067302705)
    ·
      refine ⟨59042616470417867300477029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78723488627223823067302705 59042616470417867300477029)
      ·
        refine ⟨11070490588203350118839443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59042616470417867300477029 11070490588203350118839443)
        ·
          refine ⟨16605735882305025178259165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11070490588203350118839443 16605735882305025178259165)
          ·
            refine ⟨6227150955864384441847187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16605735882305025178259165 6227150955864384441847187)
            ·
              refine ⟨9340726433796576662770781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227150955864384441847187 9340726433796576662770781)
              ·
                refine ⟨3502772412673716248539043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9340726433796576662770781 3502772412673716248539043)
                ·
                  refine ⟨5254158619010574372808565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502772412673716248539043 5254158619010574372808565)
                  ·
                    refine ⟨492577370532241347450803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5254158619010574372808565 492577370532241347450803)
                    ·
                      rfl

theorem cell23_2877873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_2877873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877873 prefixEnd_2877873 := by exact prefixLift 2877873
  have htrace : WordTrace (prefixWord ++ tailWord_2877873) baseStart_2877873 baseEnd_2877873 := by
    simpa [prefixWord, tailWord_2877873, baseEnd_2877873] using wordTrace_append hprefix tailTrace_2877873
  have hstable : (prefixWord ++ tailWord_2877873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877873).length < 2 ^ (prefixWord ++ tailWord_2877873).sum := by decide
  have hdescent : baseEnd_2877873 < baseStart_2877873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877886 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2877886 : Nat := 118140960795 + 2877886 * 2 ^ 59
def prefixEnd_2877886 : Nat := 4983230072969 + 3 ^ 40 * 2877886 * 2
def baseEnd_2877886 : Nat := 492579595615077497163283

theorem tailTrace_2877886 : CollatzResearch.WordTrace tailWord_2877886 prefixEnd_2877886 492579595615077497163283 := by
  unfold tailWord_2877886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120640706489750080411689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69976750434612000428862341 13120640706489750080411689)
  ·
    refine ⟨9840480529867312560308767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13120640706489750080411689 9840480529867312560308767)
    ·
      refine ⟨14760720794800968840463151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9840480529867312560308767 14760720794800968840463151)
      ·
        refine ⟨22141081192201453260694727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760720794800968840463151 22141081192201453260694727)
        ·
          refine ⟨33211621788302179891042091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22141081192201453260694727 33211621788302179891042091)
          ·
            refine ⟨49817432682453269836563137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33211621788302179891042091 49817432682453269836563137)
            ·
              refine ⟨37363074511839952377422353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49817432682453269836563137 37363074511839952377422353)
              ·
                refine ⟨28022305883879964283066765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37363074511839952377422353 28022305883879964283066765)
                ·
                  refine ⟨10508364706454986606150037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28022305883879964283066765 10508364706454986606150037)
                  ·
                    refine ⟨492579595615077497163283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10508364706454986606150037 492579595615077497163283)
                    ·
                      rfl

theorem cell23_2877886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2877886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877886 prefixEnd_2877886 := by exact prefixLift 2877886
  have htrace : WordTrace (prefixWord ++ tailWord_2877886) baseStart_2877886 baseEnd_2877886 := by
    simpa [prefixWord, tailWord_2877886, baseEnd_2877886] using wordTrace_append hprefix tailTrace_2877886
  have hstable : (prefixWord ++ tailWord_2877886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877886).length < 2 ^ (prefixWord ++ tailWord_2877886).sum := by decide
  have hdescent : baseEnd_2877886 < baseStart_2877886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877896 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2877896 : Nat := 118140960795 + 2877896 * 2 ^ 59
def prefixEnd_2877896 : Nat := 4983230072969 + 3 ^ 40 * 2877896 * 2
def baseEnd_2877896 : Nat := 1477743921651777452364803

theorem tailTrace_2877896 : CollatzResearch.WordTrace tailWord_2877896 prefixEnd_2877896 1477743921651777452364803 := by
  unfold tailWord_2877896
  simp only [CollatzResearch.WordTrace]
  refine ⟨52482745190940886175578771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69976993587921181567438361 52482745190940886175578771)
  ·
    refine ⟨78724117786411329263368157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52482745190940886175578771 78724117786411329263368157)
    ·
      refine ⟨29521544169904248473763059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78724117786411329263368157 29521544169904248473763059)
      ·
        refine ⟨44282316254856372710644589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29521544169904248473763059 44282316254856372710644589)
        ·
          refine ⟨16605868595571139766491721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44282316254856372710644589 16605868595571139766491721)
          ·
            refine ⟨12454401446678354824868791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16605868595571139766491721 12454401446678354824868791)
            ·
              refine ⟨18681602170017532237303187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454401446678354824868791 18681602170017532237303187)
              ·
                refine ⟨28022403255026298355954781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18681602170017532237303187 28022403255026298355954781)
                ·
                  refine ⟨10508401220634861883483043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28022403255026298355954781 10508401220634861883483043)
                  ·
                    refine ⟨15762601830952292825224565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10508401220634861883483043 15762601830952292825224565)
                    ·
                      refine ⟨1477743921651777452364803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15762601830952292825224565 1477743921651777452364803)
                      ·
                        rfl

theorem cell23_2877896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2877896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877896 prefixEnd_2877896 := by exact prefixLift 2877896
  have htrace : WordTrace (prefixWord ++ tailWord_2877896) baseStart_2877896 baseEnd_2877896 := by
    simpa [prefixWord, tailWord_2877896, baseEnd_2877896] using wordTrace_append hprefix tailTrace_2877896
  have hstable : (prefixWord ++ tailWord_2877896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877896).length < 2 ^ (prefixWord ++ tailWord_2877896).sum := by decide
  have hdescent : baseEnd_2877896 < baseStart_2877896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877899 : List Nat := [1, 1, 1, 1, 3, 3, 1, 12]
def baseStart_2877899 : Nat := 118140960795 + 2877899 * 2 ^ 59
def prefixEnd_2877899 : Nat := 4983230072969 + 3 ^ 40 * 2877899 * 2
def baseEnd_2877899 : Nat := 54731313410879294097307

theorem tailTrace_2877899 : CollatzResearch.WordTrace tailWord_2877899 prefixEnd_2877899 54731313410879294097307 := by
  unfold tailWord_2877899
  simp only [CollatzResearch.WordTrace]
  refine ⟨104965599800870903863516751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69977066533913935909011167 104965599800870903863516751)
  ·
    refine ⟨157448399701306355795275127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104965599800870903863516751 157448399701306355795275127)
    ·
      refine ⟨236172599551959533692912691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157448399701306355795275127 236172599551959533692912691)
      ·
        refine ⟨354258899327939300539369037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236172599551959533692912691 354258899327939300539369037)
        ·
          refine ⟨132847087247977237702263389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354258899327939300539369037 132847087247977237702263389)
          ·
            refine ⟨49817657717991464138348771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132847087247977237702263389 49817657717991464138348771)
            ·
              refine ⟨74726486576987196207523157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49817657717991464138348771 74726486576987196207523157)
              ·
                refine ⟨54731313410879294097307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 74726486576987196207523157 54731313410879294097307)
                ·
                  rfl

theorem cell23_2877899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 12].length) (baseStart_2877899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877899 prefixEnd_2877899 := by exact prefixLift 2877899
  have htrace : WordTrace (prefixWord ++ tailWord_2877899) baseStart_2877899 baseEnd_2877899 := by
    simpa [prefixWord, tailWord_2877899, baseEnd_2877899] using wordTrace_append hprefix tailTrace_2877899
  have hstable : (prefixWord ++ tailWord_2877899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877899).length < 2 ^ (prefixWord ++ tailWord_2877899).sum := by decide
  have hdescent : baseEnd_2877899 < baseStart_2877899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877910 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_2877910 : Nat := 118140960795 + 2877910 * 2 ^ 59
def prefixEnd_2877910 : Nat := 4983230072969 + 3 ^ 40 * 2877910 * 2
def baseEnd_2877910 : Nat := 1477751110380940397589739

theorem tailTrace_2877910 : CollatzResearch.WordTrace tailWord_2877910 prefixEnd_2877910 1477751110380940397589739 := by
  unfold tailWord_2877910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6560375062739440796385449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69977334002554035161444789 6560375062739440796385449)
  ·
    refine ⟨4920281297054580597289087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6560375062739440796385449 4920281297054580597289087)
    ·
      refine ⟨7380421945581870895933631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920281297054580597289087 7380421945581870895933631)
      ·
        refine ⟨11070632918372806343900447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380421945581870895933631 11070632918372806343900447)
        ·
          refine ⟨16605949377559209515850671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11070632918372806343900447 16605949377559209515850671)
          ·
            refine ⟨24908924066338814273776007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16605949377559209515850671 24908924066338814273776007)
            ·
              refine ⟨37363386099508221410664011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24908924066338814273776007 37363386099508221410664011)
              ·
                refine ⟨56045079149262332115996017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37363386099508221410664011 56045079149262332115996017)
                ·
                  refine ⟨42033809361946749086997013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56045079149262332115996017 42033809361946749086997013)
                  ·
                    refine ⟨1970334813841253863452985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42033809361946749086997013 1970334813841253863452985)
                    ·
                      refine ⟨1477751110380940397589739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970334813841253863452985 1477751110380940397589739)
                      ·
                        rfl

theorem cell23_2877910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_2877910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877910 prefixEnd_2877910 := by exact prefixLift 2877910
  have htrace : WordTrace (prefixWord ++ tailWord_2877910) baseStart_2877910 baseEnd_2877910 := by
    simpa [prefixWord, tailWord_2877910, baseEnd_2877910] using wordTrace_append hprefix tailTrace_2877910
  have hstable : (prefixWord ++ tailWord_2877910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877910).length < 2 ^ (prefixWord ++ tailWord_2877910).sum := by decide
  have hdescent : baseEnd_2877910 < baseStart_2877910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877930 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_2877930 : Nat := 118140960795 + 2877930 * 2 ^ 59
def prefixEnd_2877930 : Nat := 4983230072969 + 3 ^ 40 * 2877930 * 2
def baseEnd_2877930 : Nat := 1477761379994030319339647

theorem tailTrace_2877930 : CollatzResearch.WordTrace tailWord_2877930 prefixEnd_2877930 1477761379994030319339647 := by
  unfold tailWord_2877930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241682615939649039473811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69977820309172397438596829 26241682615939649039473811)
  ·
    refine ⟨39362523923909473559210717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26241682615939649039473811 39362523923909473559210717)
    ·
      refine ⟨14760946471466052584704019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39362523923909473559210717 14760946471466052584704019)
      ·
        refine ⟨22141419707199078877056029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14760946471466052584704019 22141419707199078877056029)
        ·
          refine ⟨8303032390199654578896011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22141419707199078877056029 8303032390199654578896011)
          ·
            refine ⟨12454548585299481868344017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303032390199654578896011 12454548585299481868344017)
            ·
              refine ⟨9340911438974611401258013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12454548585299481868344017 9340911438974611401258013)
              ·
                refine ⟨3502841789615479275471755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9340911438974611401258013 3502841789615479275471755)
                ·
                  refine ⟨5254262684423218913207633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502841789615479275471755 5254262684423218913207633)
                  ·
                    refine ⟨3940697013317414184905725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5254262684423218913207633 3940697013317414184905725)
                    ·
                      refine ⟨1477761379994030319339647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3940697013317414184905725 1477761379994030319339647)
                      ·
                        rfl

theorem cell23_2877930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_2877930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877930 prefixEnd_2877930 := by exact prefixLift 2877930
  have htrace : WordTrace (prefixWord ++ tailWord_2877930) baseStart_2877930 baseEnd_2877930 := by
    simpa [prefixWord, tailWord_2877930, baseEnd_2877930] using wordTrace_append hprefix tailTrace_2877930
  have hstable : (prefixWord ++ tailWord_2877930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877930).length < 2 ^ (prefixWord ++ tailWord_2877930).sum := by decide
  have hdescent : baseEnd_2877930 < baseStart_2877930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877933 : List Nat := [1, 5, 1, 3, 1, 3, 9]
def baseStart_2877933 : Nat := 118140960795 + 2877933 * 2 ^ 59
def prefixEnd_2877933 : Nat := 4983230072969 + 3 ^ 40 * 2877933 * 2
def baseEnd_2877933 : Nat := 18243986672049306266693

theorem tailTrace_2877933 : CollatzResearch.WordTrace tailWord_2877933 prefixEnd_2877933 18243986672049306266693 := by
  unfold tailWord_2877933
  simp only [CollatzResearch.WordTrace]
  refine ⟨104966839882747727670254453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69977893255165151780169635 104966839882747727670254453)
  ·
    refine ⟨9840641239007599469086355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104966839882747727670254453 9840641239007599469086355)
    ·
      refine ⟨14760961858511399203629533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9840641239007599469086355 14760961858511399203629533)
      ·
        refine ⟨5535360696941774701361075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14760961858511399203629533 5535360696941774701361075)
        ·
          refine ⟨8303041045412662052041613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535360696941774701361075 8303041045412662052041613)
          ·
            refine ⟨3113640392029748269515605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8303041045412662052041613 3113640392029748269515605)
            ·
              refine ⟨18243986672049306266693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3113640392029748269515605 18243986672049306266693)
              ·
                rfl

theorem cell23_2877933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 9].length) (baseStart_2877933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877933 prefixEnd_2877933 := by exact prefixLift 2877933
  have htrace : WordTrace (prefixWord ++ tailWord_2877933) baseStart_2877933 baseEnd_2877933 := by
    simpa [prefixWord, tailWord_2877933, baseEnd_2877933] using wordTrace_append hprefix tailTrace_2877933
  have hstable : (prefixWord ++ tailWord_2877933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877933).length < 2 ^ (prefixWord ++ tailWord_2877933).sum := by decide
  have hdescent : baseEnd_2877933 < baseStart_2877933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877944 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 1, 2, 2]
def baseStart_2877944 : Nat := 118140960795 + 2877944 * 2 ^ 59
def prefixEnd_2877944 : Nat := 4983230072969 + 3 ^ 40 * 2877944 * 2
def baseEnd_2877944 : Nat := 1477768568723193264564583

theorem tailTrace_2877944 : CollatzResearch.WordTrace tailWord_2877944 prefixEnd_2877944 1477768568723193264564583 := by
  unfold tailWord_2877944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52483620542853938274452443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69978160723805251032603257 52483620542853938274452443)
  ·
    refine ⟨78725430814280907411678665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52483620542853938274452443 78725430814280907411678665)
    ·
      refine ⟨59044073110710680558758999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78725430814280907411678665 59044073110710680558758999)
      ·
        refine ⟨88566109666066020838138499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59044073110710680558758999 88566109666066020838138499)
        ·
          refine ⟨132849164499099031257207749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88566109666066020838138499 132849164499099031257207749)
          ·
            refine ⟨24909218343581068360726453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132849164499099031257207749 24909218343581068360726453)
            ·
              refine ⟨2335239219710725158818105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24909218343581068360726453 2335239219710725158818105)
              ·
                refine ⟨1751429414783043869113579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335239219710725158818105 1751429414783043869113579)
                ·
                  refine ⟨2627144122174565803670369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751429414783043869113579 2627144122174565803670369)
                  ·
                    refine ⟨1970358091630924352752777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627144122174565803670369 1970358091630924352752777)
                    ·
                      refine ⟨1477768568723193264564583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970358091630924352752777 1477768568723193264564583)
                      ·
                        rfl

theorem cell23_2877944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_2877944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877944 prefixEnd_2877944 := by exact prefixLift 2877944
  have htrace : WordTrace (prefixWord ++ tailWord_2877944) baseStart_2877944 baseEnd_2877944 := by
    simpa [prefixWord, tailWord_2877944, baseEnd_2877944] using wordTrace_append hprefix tailTrace_2877944
  have hstable : (prefixWord ++ tailWord_2877944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877944).length < 2 ^ (prefixWord ++ tailWord_2877944).sum := by decide
  have hdescent : baseEnd_2877944 < baseStart_2877944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877996 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2877996 : Nat := 118140960795 + 2877996 * 2 ^ 59
def prefixEnd_2877996 : Nat := 4983230072969 + 3 ^ 40 * 2877996 * 2
def baseEnd_2877996 : Nat := 1477795269717227061114343

theorem tailTrace_2877996 : CollatzResearch.WordTrace tailWord_2877996 prefixEnd_2877996 1477795269717227061114343 := by
  unfold tailWord_2877996
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484568840759744714898921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69979425121012992953198561 52484568840759744714898921)
  ·
    refine ⟨39363426630569808536174191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52484568840759744714898921 39363426630569808536174191)
    ·
      refine ⟨59045139945854712804261287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39363426630569808536174191 59045139945854712804261287)
      ·
        refine ⟨88567709918782069206391931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59045139945854712804261287 88567709918782069206391931)
        ·
          refine ⟨132851564878173103809587897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88567709918782069206391931 132851564878173103809587897)
          ·
            refine ⟨99638673658629827857190923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132851564878173103809587897 99638673658629827857190923)
            ·
              refine ⟨149458010487944741785786385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99638673658629827857190923 149458010487944741785786385)
              ·
                refine ⟨112093507865958556339339789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149458010487944741785786385 112093507865958556339339789)
                ·
                  refine ⟨42035065449734458627252421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112093507865958556339339789 42035065449734458627252421)
                  ·
                    refine ⟨7881574771825210992609829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42035065449734458627252421 7881574771825210992609829)
                    ·
                      refine ⟨1477795269717227061114343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7881574771825210992609829 1477795269717227061114343)
                      ·
                        rfl

theorem cell23_2877996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2877996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2877996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2877996 prefixEnd_2877996 := by exact prefixLift 2877996
  have htrace : WordTrace (prefixWord ++ tailWord_2877996) baseStart_2877996 baseEnd_2877996 := by
    simpa [prefixWord, tailWord_2877996, baseEnd_2877996] using wordTrace_append hprefix tailTrace_2877996
  have hstable : (prefixWord ++ tailWord_2877996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877996).length < 2 ^ (prefixWord ++ tailWord_2877996).sum := by decide
  have hdescent : baseEnd_2877996 < baseStart_2877996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878000 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2]
def baseStart_2878000 : Nat := 118140960795 + 2878000 * 2 ^ 59
def prefixEnd_2878000 : Nat := 4983230072969 + 3 ^ 40 * 2878000 * 2
def baseEnd_2878000 : Nat := 1477797323639845045464325

theorem tailTrace_2878000 : CollatzResearch.WordTrace tailWord_2878000 prefixEnd_2878000 1477797323639845045464325 := by
  unfold tailWord_2878000
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484641786752499056471727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69979522382336665408628969 52484641786752499056471727)
  ·
    refine ⟨78726962680128748584707591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52484641786752499056471727 78726962680128748584707591)
    ·
      refine ⟨118090444020193122877061387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78726962680128748584707591 118090444020193122877061387)
      ·
        refine ⟨177135666030289684315592081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118090444020193122877061387 177135666030289684315592081)
        ·
          refine ⟨132851749522717263236694061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177135666030289684315592081 132851749522717263236694061)
          ·
            refine ⟨49819406071018973713760273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132851749522717263236694061 49819406071018973713760273)
            ·
              refine ⟨37364554553264230285320205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49819406071018973713760273 37364554553264230285320205)
              ·
                refine ⟨14011707957474086356995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37364554553264230285320205 14011707957474086356995077)
                ·
                  refine ⟨2627195242026391191936577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14011707957474086356995077 2627195242026391191936577)
                  ·
                    refine ⟨1970396431519793393952433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627195242026391191936577 1970396431519793393952433)
                    ·
                      refine ⟨1477797323639845045464325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970396431519793393952433 1477797323639845045464325)
                      ·
                        rfl

theorem cell23_2878000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2].length) (baseStart_2878000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878000 prefixEnd_2878000 := by exact prefixLift 2878000
  have htrace : WordTrace (prefixWord ++ tailWord_2878000) baseStart_2878000 baseEnd_2878000 := by
    simpa [prefixWord, tailWord_2878000, baseEnd_2878000] using wordTrace_append hprefix tailTrace_2878000
  have hstable : (prefixWord ++ tailWord_2878000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878000).length < 2 ^ (prefixWord ++ tailWord_2878000).sum := by decide
  have hdescent : baseEnd_2878000 < baseStart_2878000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878013 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2878013 : Nat := 118140960795 + 2878013 * 2 ^ 59
def prefixEnd_2878013 : Nat := 4983230072969 + 3 ^ 40 * 2878013 * 2
def baseEnd_2878013 : Nat := 1477803998888353494601765

theorem tailTrace_2878013 : CollatzResearch.WordTrace tailWord_2878013 prefixEnd_2878013 1477803998888353494601765 := by
  unfold tailWord_2878013
  simp only [CollatzResearch.WordTrace]
  refine ⟨104969757722457901333166693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69979838481638600888777795 104969757722457901333166693)
  ·
    refine ⟨19681829572960856499968755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104969757722457901333166693 19681829572960856499968755)
    ·
      refine ⟨29522744359441284749953133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19681829572960856499968755 29522744359441284749953133)
      ·
        refine ⟨11071029134790481781232425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29522744359441284749953133 11071029134790481781232425)
        ·
          refine ⟨8303271851092861335924319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11071029134790481781232425 8303271851092861335924319)
          ·
            refine ⟨12454907776639292003886479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8303271851092861335924319 12454907776639292003886479)
            ·
              refine ⟨18682361664958938005829719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454907776639292003886479 18682361664958938005829719)
              ·
                refine ⟨28023542497438407008744579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18682361664958938005829719 28023542497438407008744579)
                ·
                  refine ⟨42035313746157610513116869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28023542497438407008744579 42035313746157610513116869)
                  ·
                    refine ⟨7881621327404551971209413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42035313746157610513116869 7881621327404551971209413)
                    ·
                      refine ⟨1477803998888353494601765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7881621327404551971209413 1477803998888353494601765)
                      ·
                        rfl

theorem cell23_2878013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2878013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878013 prefixEnd_2878013 := by exact prefixLift 2878013
  have htrace : WordTrace (prefixWord ++ tailWord_2878013) baseStart_2878013 baseEnd_2878013 := by
    simpa [prefixWord, tailWord_2878013, baseEnd_2878013] using wordTrace_append hprefix tailTrace_2878013
  have hstable : (prefixWord ++ tailWord_2878013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878013).length < 2 ^ (prefixWord ++ tailWord_2878013).sum := by decide
  have hdescent : baseEnd_2878013 < baseStart_2878013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878017 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_2878017 : Nat := 118140960795 + 2878017 * 2 ^ 59
def prefixEnd_2878017 : Nat := 4983230072969 + 3 ^ 40 * 2878017 * 2
def baseEnd_2878017 : Nat := 1477806052810971478951747

theorem tailTrace_2878017 : CollatzResearch.WordTrace tailWord_2878017 prefixEnd_2878017 1477806052810971478951747 := by
  unfold tailWord_2878017
  simp only [CollatzResearch.WordTrace]
  refine ⟨104969903614443410016312305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69979935742962273344208203 104969903614443410016312305)
  ·
    refine ⟨78727427710832557512234229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104969903614443410016312305 78727427710832557512234229)
    ·
      refine ⟨7380696347890552266771959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78727427710832557512234229 7380696347890552266771959)
      ·
        refine ⟨11071044521835828400157939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380696347890552266771959 11071044521835828400157939)
        ·
          refine ⟨16606566782753742600236909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11071044521835828400157939 16606566782753742600236909)
          ·
            refine ⟨6227462543532653475088841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16606566782753742600236909 6227462543532653475088841)
            ·
              refine ⟨4670596907649490106316631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227462543532653475088841 4670596907649490106316631)
              ·
                refine ⟨7005895361474235159474947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670596907649490106316631 7005895361474235159474947)
                ·
                  refine ⟨10508843042211352739212421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005895361474235159474947 10508843042211352739212421)
                  ·
                    refine ⟨1970408070414628638602329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10508843042211352739212421 1970408070414628638602329)
                    ·
                      refine ⟨1477806052810971478951747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970408070414628638602329 1477806052810971478951747)
                      ·
                        rfl

theorem cell23_2878017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_2878017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878017 prefixEnd_2878017 := by exact prefixLift 2878017
  have htrace : WordTrace (prefixWord ++ tailWord_2878017) baseStart_2878017 baseEnd_2878017 := by
    simpa [prefixWord, tailWord_2878017, baseEnd_2878017] using wordTrace_append hprefix tailTrace_2878017
  have hstable : (prefixWord ++ tailWord_2878017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878017).length < 2 ^ (prefixWord ++ tailWord_2878017).sum := by decide
  have hdescent : baseEnd_2878017 < baseStart_2878017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878023 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 7]
def baseStart_2878023 : Nat := 118140960795 + 2878023 * 2 ^ 59
def prefixEnd_2878023 : Nat := 4983230072969 + 3 ^ 40 * 2878023 * 2
def baseEnd_2878023 : Nat := 164201014854988717275191

theorem tailTrace_2878023 : CollatzResearch.WordTrace tailWord_2878023 prefixEnd_2878023 164201014854988717275191 := by
  unfold tailWord_2878023
  simp only [CollatzResearch.WordTrace]
  refine ⟨104970122452421673041030723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69980081634947782027353815 104970122452421673041030723)
  ·
    refine ⟨157455183678632509561546085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104970122452421673041030723 157455183678632509561546085)
    ·
      refine ⟨29522846939743595542789891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157455183678632509561546085 29522846939743595542789891)
      ·
        refine ⟨44284270409615393314184837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29522846939743595542789891 44284270409615393314184837)
        ·
          refine ⟨8303300701802886246409657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44284270409615393314184837 8303300701802886246409657)
          ·
            refine ⟨6227475526352164684807243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8303300701802886246409657 6227475526352164684807243)
            ·
              refine ⟨9341213289528247027210865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227475526352164684807243 9341213289528247027210865)
              ·
                refine ⟨7005909967146185270408149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9341213289528247027210865 7005909967146185270408149)
                ·
                  refine ⟨164201014854988717275191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7005909967146185270408149 164201014854988717275191)
                  ·
                    rfl

theorem cell23_2878023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 7].length) (baseStart_2878023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878023 prefixEnd_2878023 := by exact prefixLift 2878023
  have htrace : WordTrace (prefixWord ++ tailWord_2878023) baseStart_2878023 baseEnd_2878023 := by
    simpa [prefixWord, tailWord_2878023, baseEnd_2878023] using wordTrace_append hprefix tailTrace_2878023
  have hstable : (prefixWord ++ tailWord_2878023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878023).length < 2 ^ (prefixWord ++ tailWord_2878023).sum := by decide
  have hdescent : baseEnd_2878023 < baseStart_2878023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878073 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2878073 : Nat := 118140960795 + 2878073 * 2 ^ 59
def prefixEnd_2878073 : Nat := 4983230072969 + 3 ^ 40 * 2878073 * 2
def baseEnd_2878073 : Nat := 1477834807727623259851489

theorem tailTrace_2878073 : CollatzResearch.WordTrace tailWord_2878073 prefixEnd_2878073 1477834807727623259851489 := by
  unfold tailWord_2878073
  simp only [CollatzResearch.WordTrace]
  refine ⟨104971946102240531580350873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69981297401493687720233915 104971946102240531580350873)
  ·
    refine ⟨78728959576680398685263155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104971946102240531580350873 78728959576680398685263155)
    ·
      refine ⟨118093439365020598027894733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78728959576680398685263155 118093439365020598027894733)
      ·
        refine ⟨44285039761882724260460525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118093439365020598027894733 44285039761882724260460525)
        ·
          refine ⟨16606889910706021597672697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44285039761882724260460525 16606889910706021597672697)
          ·
            refine ⟨12455167433029516198254523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16606889910706021597672697 12455167433029516198254523)
            ·
              refine ⟨18682751149544274297381785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455167433029516198254523 18682751149544274297381785)
              ·
                refine ⟨14012063362158205723036339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18682751149544274297381785 14012063362158205723036339)
                ·
                  refine ⟨21018095043237308584554509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14012063362158205723036339 21018095043237308584554509)
                  ·
                    refine ⟨7881785641213990719207941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21018095043237308584554509 7881785641213990719207941)
                    ·
                      refine ⟨1477834807727623259851489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7881785641213990719207941 1477834807727623259851489)
                      ·
                        rfl

theorem cell23_2878073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2878073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878073 prefixEnd_2878073 := by exact prefixLift 2878073
  have htrace : WordTrace (prefixWord ++ tailWord_2878073) baseStart_2878073 baseEnd_2878073 := by
    simpa [prefixWord, tailWord_2878073, baseEnd_2878073] using wordTrace_append hprefix tailTrace_2878073
  have hstable : (prefixWord ++ tailWord_2878073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878073).length < 2 ^ (prefixWord ++ tailWord_2878073).sum := by decide
  have hdescent : baseEnd_2878073 < baseStart_2878073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878167 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_2878167 : Nat := 118140960795 + 2878167 * 2 ^ 59
def prefixEnd_2878167 : Nat := 4983230072969 + 3 ^ 40 * 2878167 * 2
def baseEnd_2878167 : Nat := 1477883074909145892076057

theorem tailTrace_2878167 : CollatzResearch.WordTrace tailWord_2878167 prefixEnd_2878167 1477883074909145892076057 := by
  unfold tailWord_2878167
  simp only [CollatzResearch.WordTrace]
  refine ⟨104975374563899985634272755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69983583042599990422848503 104975374563899985634272755)
  ·
    refine ⟨157463061845849978451409133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104975374563899985634272755 157463061845849978451409133)
    ·
      refine ⟨59048648192193741919278425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157463061845849978451409133 59048648192193741919278425)
      ·
        refine ⟨44286486144145306439458819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59048648192193741919278425 44286486144145306439458819)
        ·
          refine ⟨66429729216217959659188229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44286486144145306439458819 66429729216217959659188229)
          ·
            refine ⟨12455574228040867436097793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66429729216217959659188229 12455574228040867436097793)
            ·
              refine ⟨9341680671030650577073345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12455574228040867436097793 9341680671030650577073345)
              ·
                refine ⟨7006260503272987932805009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9341680671030650577073345 7006260503272987932805009)
                ·
                  refine ⟨5254695377454740949603757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006260503272987932805009 5254695377454740949603757)
                  ·
                    refine ⟨1970510766545527856101409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5254695377454740949603757 1970510766545527856101409)
                    ·
                      refine ⟨1477883074909145892076057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970510766545527856101409 1477883074909145892076057)
                      ·
                        rfl

theorem cell23_2878167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_2878167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878167 prefixEnd_2878167 := by exact prefixLift 2878167
  have htrace : WordTrace (prefixWord ++ tailWord_2878167) baseStart_2878167 baseEnd_2878167 := by
    simpa [prefixWord, tailWord_2878167, baseEnd_2878167] using wordTrace_append hprefix tailTrace_2878167
  have hstable : (prefixWord ++ tailWord_2878167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878167).length < 2 ^ (prefixWord ++ tailWord_2878167).sum := by decide
  have hdescent : baseEnd_2878167 < baseStart_2878167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878180 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2878180 : Nat := 118140960795 + 2878180 * 2 ^ 59
def prefixEnd_2878180 : Nat := 4983230072969 + 3 ^ 40 * 2878180 * 2
def baseEnd_2878180 : Nat := 1477889750157654341213497

theorem tailTrace_2878180 : CollatzResearch.WordTrace tailWord_2878180 prefixEnd_2878180 1477889750157654341213497 := by
  unfold tailWord_2878180
  simp only [CollatzResearch.WordTrace]
  refine ⟨52487924356426444427247997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69983899141901925902997329 52487924356426444427247997)
  ·
    refine ⟨19682971633659916660217999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52487924356426444427247997 19682971633659916660217999)
    ·
      refine ⟨29524457450489874990326999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19682971633659916660217999 29524457450489874990326999)
      ·
        refine ⟨44286686175734812485490499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29524457450489874990326999 44286686175734812485490499)
        ·
          refine ⟨66430029263602218728235749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44286686175734812485490499 66430029263602218728235749)
          ·
            refine ⟨12455630486925416011544203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66430029263602218728235749 12455630486925416011544203)
            ·
              refine ⟨18683445730388124017316305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455630486925416011544203 18683445730388124017316305)
              ·
                refine ⟨14012584297791093012987229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18683445730388124017316305 14012584297791093012987229)
                ·
                  refine ⟨5254719111671659879870211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14012584297791093012987229 5254719111671659879870211)
                  ·
                    refine ⟨7882078667507489819805317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5254719111671659879870211 7882078667507489819805317)
                    ·
                      refine ⟨1477889750157654341213497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7882078667507489819805317 1477889750157654341213497)
                      ·
                        rfl

theorem cell23_2878180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2878180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878180 prefixEnd_2878180 := by exact prefixLift 2878180
  have htrace : WordTrace (prefixWord ++ tailWord_2878180) baseStart_2878180 baseEnd_2878180 := by
    simpa [prefixWord, tailWord_2878180, baseEnd_2878180] using wordTrace_append hprefix tailTrace_2878180
  have hstable : (prefixWord ++ tailWord_2878180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878180).length < 2 ^ (prefixWord ++ tailWord_2878180).sum := by decide
  have hdescent : baseEnd_2878180 < baseStart_2878180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878190 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2878190 : Nat := 118140960795 + 2878190 * 2 ^ 59
def prefixEnd_2878190 : Nat := 4983230072969 + 3 ^ 40 * 2878190 * 2
def baseEnd_2878190 : Nat := 492631628321399767362817

theorem tailTrace_2878190 : CollatzResearch.WordTrace tailWord_2878190 prefixEnd_2878190 492631628321399767362817 := by
  unfold tailWord_2878190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122026680352082570295003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69984142295211107041573349 13122026680352082570295003)
  ·
    refine ⟨19683040020528123855442505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13122026680352082570295003 19683040020528123855442505)
    ·
      refine ⟨14762280015396092891581879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19683040020528123855442505 14762280015396092891581879)
      ·
        refine ⟨22143420023094139337372819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14762280015396092891581879 22143420023094139337372819)
        ·
          refine ⟨33215130034641209006059229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22143420023094139337372819 33215130034641209006059229)
          ·
            refine ⟨12455673762990453377272211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33215130034641209006059229 12455673762990453377272211)
            ·
              refine ⟨18683510644485680065908317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455673762990453377272211 18683510644485680065908317)
              ·
                refine ⟨7006316491682130024715619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18683510644485680065908317 7006316491682130024715619)
                ·
                  refine ⟨10509474737523195037073429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006316491682130024715619 10509474737523195037073429)
                  ·
                    refine ⟨492631628321399767362817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10509474737523195037073429 492631628321399767362817)
                    ·
                      rfl

theorem cell23_2878190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2878190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878190 prefixEnd_2878190 := by exact prefixLift 2878190
  have htrace : WordTrace (prefixWord ++ tailWord_2878190) baseStart_2878190 baseEnd_2878190 := by
    simpa [prefixWord, tailWord_2878190, baseEnd_2878190] using wordTrace_append hprefix tailTrace_2878190
  have hstable : (prefixWord ++ tailWord_2878190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878190).length < 2 ^ (prefixWord ++ tailWord_2878190).sum := by decide
  have hdescent : baseEnd_2878190 < baseStart_2878190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878200 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_2878200 : Nat := 118140960795 + 2878200 * 2 ^ 59
def prefixEnd_2878200 : Nat := 4983230072969 + 3 ^ 40 * 2878200 * 2
def baseEnd_2878200 : Nat := 1477900019770744262963405

theorem tailTrace_2878200 : CollatzResearch.WordTrace tailWord_2878200 prefixEnd_2878200 1477900019770744262963405 := by
  unfold tailWord_2878200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52488289086390216135112027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69984385448520288180149369 52488289086390216135112027)
  ·
    refine ⟨78732433629585324202668041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52488289086390216135112027 78732433629585324202668041)
    ·
      refine ⟨59049325222188993152001031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78732433629585324202668041 59049325222188993152001031)
      ·
        refine ⟨88573987833283489728001547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59049325222188993152001031 88573987833283489728001547)
        ·
          refine ⟨132860981749925234592002321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88573987833283489728001547 132860981749925234592002321)
          ·
            refine ⟨99645736312443925944001741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132860981749925234592002321 99645736312443925944001741)
            ·
              refine ⟨37367151117166472229000653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99645736312443925944001741 37367151117166472229000653)
              ·
                refine ⟨14012681668937427085875245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37367151117166472229000653 14012681668937427085875245)
                ·
                  refine ⟨5254755625851535157203217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14012681668937427085875245 5254755625851535157203217)
                  ·
                    refine ⟨3941066719388651367902413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5254755625851535157203217 3941066719388651367902413)
                    ·
                      refine ⟨1477900019770744262963405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3941066719388651367902413 1477900019770744262963405)
                      ·
                        rfl

theorem cell23_2878200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_2878200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878200 prefixEnd_2878200 := by exact prefixLift 2878200
  have htrace : WordTrace (prefixWord ++ tailWord_2878200) baseStart_2878200 baseEnd_2878200 := by
    simpa [prefixWord, tailWord_2878200, baseEnd_2878200] using wordTrace_append hprefix tailTrace_2878200
  have hstable : (prefixWord ++ tailWord_2878200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878200).length < 2 ^ (prefixWord ++ tailWord_2878200).sum := by decide
  have hdescent : baseEnd_2878200 < baseStart_2878200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878231 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2878231 : Nat := 118140960795 + 2878231 * 2 ^ 59
def prefixEnd_2878231 : Nat := 4983230072969 + 3 ^ 40 * 2878231 * 2
def baseEnd_2878231 : Nat := 1477915937671033641675763

theorem tailTrace_2878231 : CollatzResearch.WordTrace tailWord_2878231 prefixEnd_2878231 1477915937671033641675763 := by
  unfold tailWord_2878231
  simp only [CollatzResearch.WordTrace]
  refine ⟨104977708835668124564602547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69985139223778749709735031 104977708835668124564602547)
  ·
    refine ⟨157466563253502186846903821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104977708835668124564602547 157466563253502186846903821)
    ·
      refine ⟨59049961220063320067588933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157466563253502186846903821 59049961220063320067588933)
      ·
        refine ⟨11071867728761872512672925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59049961220063320067588933 11071867728761872512672925)
        ·
          refine ⟨4151950398285702192252347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11071867728761872512672925 4151950398285702192252347)
          ·
            refine ⟨6227925597428553288378521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151950398285702192252347 6227925597428553288378521)
            ·
              refine ⟨4670944198071414966283891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227925597428553288378521 4670944198071414966283891)
              ·
                refine ⟨7006416297107122449425837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670944198071414966283891 7006416297107122449425837)
                ·
                  refine ⟨2627406111415170918534689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7006416297107122449425837 2627406111415170918534689)
                  ·
                    refine ⟨1970554583561378188901017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627406111415170918534689 1970554583561378188901017)
                    ·
                      refine ⟨1477915937671033641675763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970554583561378188901017 1477915937671033641675763)
                      ·
                        rfl

theorem cell23_2878231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2878231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878231 prefixEnd_2878231 := by exact prefixLift 2878231
  have htrace : WordTrace (prefixWord ++ tailWord_2878231) baseStart_2878231 baseEnd_2878231 := by
    simpa [prefixWord, tailWord_2878231, baseEnd_2878231] using wordTrace_append hprefix tailTrace_2878231
  have hstable : (prefixWord ++ tailWord_2878231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878231).length < 2 ^ (prefixWord ++ tailWord_2878231).sum := by decide
  have hdescent : baseEnd_2878231 < baseStart_2878231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878233 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_2878233 : Nat := 118140960795 + 2878233 * 2 ^ 59
def prefixEnd_2878233 : Nat := 4983230072969 + 3 ^ 40 * 2878233 * 2
def baseEnd_2878233 : Nat := 492638988210780877950251

theorem tailTrace_2878233 : CollatzResearch.WordTrace tailWord_2878233 prefixEnd_2878233 492638988210780877950251 := by
  unfold tailWord_2878233
  simp only [CollatzResearch.WordTrace]
  refine ⟨104977781781660878906175353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69985187854440585937450235 104977781781660878906175353)
  ·
    refine ⟨78733336336245659179631515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104977781781660878906175353 78733336336245659179631515)
    ·
      refine ⟨118100004504368488769447273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78733336336245659179631515 118100004504368488769447273)
      ·
        refine ⟨88575003378276366577085455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118100004504368488769447273 88575003378276366577085455)
        ·
          refine ⟨132862505067414549865628183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88575003378276366577085455 132862505067414549865628183)
          ·
            refine ⟨199293757601121824798442275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132862505067414549865628183 199293757601121824798442275)
            ·
              refine ⟨298940636401682737197663413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199293757601121824798442275 298940636401682737197663413)
              ·
                refine ⟨28025684662657756612280945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298940636401682737197663413 28025684662657756612280945)
                ·
                  refine ⟨21019263496993317459210709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28025684662657756612280945 21019263496993317459210709)
                  ·
                    refine ⟨492638988210780877950251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21019263496993317459210709 492638988210780877950251)
                    ·
                      rfl

theorem cell23_2878233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_2878233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878233 prefixEnd_2878233 := by exact prefixLift 2878233
  have htrace : WordTrace (prefixWord ++ tailWord_2878233) baseStart_2878233 baseEnd_2878233 := by
    simpa [prefixWord, tailWord_2878233, baseEnd_2878233] using wordTrace_append hprefix tailTrace_2878233
  have hstable : (prefixWord ++ tailWord_2878233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878233).length < 2 ^ (prefixWord ++ tailWord_2878233).sum := by decide
  have hdescent : baseEnd_2878233 < baseStart_2878233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878244 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2878244 : Nat := 118140960795 + 2878244 * 2 ^ 59
def prefixEnd_2878244 : Nat := 4983230072969 + 3 ^ 40 * 2878244 * 2
def baseEnd_2878244 : Nat := 1477922612919542090813203

theorem tailTrace_2878244 : CollatzResearch.WordTrace tailWord_2878244 prefixEnd_2878244 1477922612919542090813203 := by
  unfold tailWord_2878244
  simp only [CollatzResearch.WordTrace]
  refine ⟨52489091492310513892412893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69985455323080685189883857 52489091492310513892412893)
  ·
    refine ⟨19683409309616442709654835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52489091492310513892412893 19683409309616442709654835)
    ·
      refine ⟨29525113964424664064482253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19683409309616442709654835 29525113964424664064482253)
      ·
        refine ⟨11071917736659249024180845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29525113964424664064482253 11071917736659249024180845)
        ·
          refine ⟨4151969151247218384067817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11071917736659249024180845 4151969151247218384067817)
          ·
            refine ⟨3113976863435413788050863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151969151247218384067817 3113976863435413788050863)
            ·
              refine ⟨4670965295153120682076295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113976863435413788050863 4670965295153120682076295)
              ·
                refine ⟨7006447942729681023114443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670965295153120682076295 7006447942729681023114443)
                ·
                  refine ⟨10509671914094521534671665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7006447942729681023114443 10509671914094521534671665)
                  ·
                    refine ⟨7882253935570891151003749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10509671914094521534671665 7882253935570891151003749)
                    ·
                      refine ⟨1477922612919542090813203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7882253935570891151003749 1477922612919542090813203)
                      ·
                        rfl

theorem cell23_2878244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2878244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878244 prefixEnd_2878244 := by exact prefixLift 2878244
  have htrace : WordTrace (prefixWord ++ tailWord_2878244) baseStart_2878244 baseEnd_2878244 := by
    simpa [prefixWord, tailWord_2878244, baseEnd_2878244] using wordTrace_append hprefix tailTrace_2878244
  have hstable : (prefixWord ++ tailWord_2878244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878244).length < 2 ^ (prefixWord ++ tailWord_2878244).sum := by decide
  have hdescent : baseEnd_2878244 < baseStart_2878244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878254 : List Nat := [4, 1, 3, 2, 1, 3, 2, 7]
def baseStart_2878254 : Nat := 118140960795 + 2878254 * 2 ^ 59
def prefixEnd_2878254 : Nat := 4983230072969 + 3 ^ 40 * 2878254 * 2
def baseEnd_2878254 : Nat := 54738064730595816729191

theorem tailTrace_2878254 : CollatzResearch.WordTrace tailWord_2878254 prefixEnd_2878254 54738064730595816729191 := by
  unfold tailWord_2878254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122318464323099936586227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69985698476389866328459877 13122318464323099936586227)
  ·
    refine ⟨19683477696484649904879341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13122318464323099936586227 19683477696484649904879341)
    ·
      refine ⟨7381304136181743714329753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19683477696484649904879341 7381304136181743714329753)
      ·
        refine ⟨5535978102136307785747315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381304136181743714329753 5535978102136307785747315)
        ·
          refine ⟨8303967153204461678620973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535978102136307785747315 8303967153204461678620973)
          ·
            refine ⟨3113987682451673129482865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8303967153204461678620973 3113987682451673129482865)
            ·
              refine ⟨2335490761838754847112149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113987682451673129482865 2335490761838754847112149)
              ·
                refine ⟨54738064730595816729191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2335490761838754847112149 54738064730595816729191)
                ·
                  rfl

theorem cell23_2878254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_2878254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878254 prefixEnd_2878254 := by exact prefixLift 2878254
  have htrace : WordTrace (prefixWord ++ tailWord_2878254) baseStart_2878254 baseEnd_2878254 := by
    simpa [prefixWord, tailWord_2878254, baseEnd_2878254] using wordTrace_append hprefix tailTrace_2878254
  have hstable : (prefixWord ++ tailWord_2878254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878254).length < 2 ^ (prefixWord ++ tailWord_2878254).sum := by decide
  have hdescent : baseEnd_2878254 < baseStart_2878254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878290 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2878290 : Nat := 118140960795 + 2878290 * 2 ^ 59
def prefixEnd_2878290 : Nat := 4983230072969 + 3 ^ 40 * 2878290 * 2
def baseEnd_2878290 : Nat := 1477946233029648910837991

theorem tailTrace_2878290 : CollatzResearch.WordTrace tailWord_2878290 prefixEnd_2878290 1477946233029648910837991 := by
  unfold tailWord_2878290
  simp only [CollatzResearch.WordTrace]
  refine ⟨26244965185613594410250081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69986573828302918427333549 26244965185613594410250081)
  ·
    refine ⟨19683723889210195807687561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26244965185613594410250081 19683723889210195807687561)
    ·
      refine ⟨14762792916907646855765671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19683723889210195807687561 14762792916907646855765671)
      ·
        refine ⟨22144189375361470283648507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14762792916907646855765671 22144189375361470283648507)
        ·
          refine ⟨33216284063042205425472761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22144189375361470283648507 33216284063042205425472761)
          ·
            refine ⟨24912213047281654069104571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33216284063042205425472761 24912213047281654069104571)
            ·
              refine ⟨37368319570922481103656857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24912213047281654069104571 37368319570922481103656857)
              ·
                refine ⟨28026239678191860827742643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37368319570922481103656857 28026239678191860827742643)
                ·
                  refine ⟨42039359517287791241613965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28026239678191860827742643 42039359517287791241613965)
                  ·
                    refine ⟨15764759818982921715605237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42039359517287791241613965 15764759818982921715605237)
                    ·
                      refine ⟨1477946233029648910837991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15764759818982921715605237 1477946233029648910837991)
                      ·
                        rfl

theorem cell23_2878290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2878290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878290 prefixEnd_2878290 := by exact prefixLift 2878290
  have htrace : WordTrace (prefixWord ++ tailWord_2878290) baseStart_2878290 baseEnd_2878290 := by
    simpa [prefixWord, tailWord_2878290, baseEnd_2878290] using wordTrace_append hprefix tailTrace_2878290
  have hstable : (prefixWord ++ tailWord_2878290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878290).length < 2 ^ (prefixWord ++ tailWord_2878290).sum := by decide
  have hdescent : baseEnd_2878290 < baseStart_2878290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878340 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2878340 : Nat := 118140960795 + 2878340 * 2 ^ 59
def prefixEnd_2878340 : Nat := 4983230072969 + 3 ^ 40 * 2878340 * 2
def baseEnd_2878340 : Nat := 492657302354124571737587

theorem tailTrace_2878340 : CollatzResearch.WordTrace tailWord_2878340 prefixEnd_2878340 492657302354124571737587 := by
  unfold tailWord_2878340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52490842196136618090160237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69987789594848824120213649 52490842196136618090160237)
  ·
    refine ⟨19684065823551231783810089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52490842196136618090160237 19684065823551231783810089)
    ·
      refine ⟨14763049367663423837857567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19684065823551231783810089 14763049367663423837857567)
      ·
        refine ⟨22144574051495135756786351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14763049367663423837857567 22144574051495135756786351)
        ·
          refine ⟨33216861077242703635179527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22144574051495135756786351 33216861077242703635179527)
          ·
            refine ⟨49825291615864055452769291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33216861077242703635179527 49825291615864055452769291)
            ·
              refine ⟨74737937423796083179153937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49825291615864055452769291 74737937423796083179153937)
              ·
                refine ⟨56053453067847062384365453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74737937423796083179153937 56053453067847062384365453)
                ·
                  refine ⟨21020044900442648394137045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56053453067847062384365453 21020044900442648394137045)
                  ·
                    refine ⟨492657302354124571737587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21020044900442648394137045 492657302354124571737587)
                    ·
                      rfl

theorem cell23_2878340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2878340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878340 prefixEnd_2878340 := by exact prefixLift 2878340
  have htrace : WordTrace (prefixWord ++ tailWord_2878340) baseStart_2878340 baseEnd_2878340 := by
    simpa [prefixWord, tailWord_2878340, baseEnd_2878340] using wordTrace_append hprefix tailTrace_2878340
  have hstable : (prefixWord ++ tailWord_2878340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878340).length < 2 ^ (prefixWord ++ tailWord_2878340).sum := by decide
  have hdescent : baseEnd_2878340 < baseStart_2878340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878344 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 5]
def baseStart_2878344 : Nat := 118140960795 + 2878344 * 2 ^ 59
def prefixEnd_2878344 : Nat := 4983230072969 + 3 ^ 40 * 2878344 * 2
def baseEnd_2878344 : Nat := 164219328998332411062527

theorem tailTrace_2878344 : CollatzResearch.WordTrace tailWord_2878344 prefixEnd_2878344 164219328998332411062527 := by
  unfold tailWord_2878344
  simp only [CollatzResearch.WordTrace]
  refine ⟨52490915142129372431733043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69987886856172496575644057 52490915142129372431733043)
  ·
    refine ⟨78736372713194058647599565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52490915142129372431733043 78736372713194058647599565)
    ·
      refine ⟨29526139767447771992849837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78736372713194058647599565 29526139767447771992849837)
      ·
        refine ⟨11072302412792914497318689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29526139767447771992849837 11072302412792914497318689)
        ·
          refine ⟨8304226809594685872989017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11072302412792914497318689 8304226809594685872989017)
          ·
            refine ⟨6228170107196014404741763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304226809594685872989017 6228170107196014404741763)
            ·
              refine ⟨9342255160794021607112645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228170107196014404741763 9342255160794021607112645)
              ·
                refine ⟨1751672842648879051333621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9342255160794021607112645 1751672842648879051333621)
                ·
                  refine ⟨164219328998332411062527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1751672842648879051333621 164219328998332411062527)
                  ·
                    rfl

theorem cell23_2878344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 5].length) (baseStart_2878344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878344 prefixEnd_2878344 := by exact prefixLift 2878344
  have htrace : WordTrace (prefixWord ++ tailWord_2878344) baseStart_2878344 baseEnd_2878344 := by
    simpa [prefixWord, tailWord_2878344, baseEnd_2878344] using wordTrace_append hprefix tailTrace_2878344
  have hstable : (prefixWord ++ tailWord_2878344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878344).length < 2 ^ (prefixWord ++ tailWord_2878344).sum := by decide
  have hdescent : baseEnd_2878344 < baseStart_2878344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878347 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 5, 2]
def baseStart_2878347 : Nat := 118140960795 + 2878347 * 2 ^ 59
def prefixEnd_2878347 : Nat := 4983230072969 + 3 ^ 40 * 2878347 * 2
def baseEnd_2878347 : Nat := 1477975501426955187825229

theorem tailTrace_2878347 : CollatzResearch.WordTrace tailWord_2878347 prefixEnd_2878347 1477975501426955187825229 := by
  unfold tailWord_2878347
  simp only [CollatzResearch.WordTrace]
  refine ⟨104981939703247876375825295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69987959802165250917216863 104981939703247876375825295)
  ·
    refine ⟨157472909554871814563737943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104981939703247876375825295 157472909554871814563737943)
    ·
      refine ⟨236209364332307721845606915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157472909554871814563737943 236209364332307721845606915)
      ·
        refine ⟨354314046498461582768410373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236209364332307721845606915 354314046498461582768410373)
        ·
          refine ⟨66433883718461546769076945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354314046498461582768410373 66433883718461546769076945)
          ·
            refine ⟨49825412788846160076807709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66433883718461546769076945 49825412788846160076807709)
            ·
              refine ⟨18684529795817310028802891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49825412788846160076807709 18684529795817310028802891)
              ·
                refine ⟨28026794693725965043204337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18684529795817310028802891 28026794693725965043204337)
                ·
                  refine ⟨21020096020294473782403253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28026794693725965043204337 21020096020294473782403253)
                  ·
                    refine ⟨1970634001902606917100305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21020096020294473782403253 1970634001902606917100305)
                    ·
                      refine ⟨1477975501426955187825229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970634001902606917100305 1477975501426955187825229)
                      ·
                        rfl

theorem cell23_2878347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5, 2].length) (baseStart_2878347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878347 prefixEnd_2878347 := by exact prefixLift 2878347
  have htrace : WordTrace (prefixWord ++ tailWord_2878347) baseStart_2878347 baseEnd_2878347 := by
    simpa [prefixWord, tailWord_2878347, baseEnd_2878347] using wordTrace_append hprefix tailTrace_2878347
  have hstable : (prefixWord ++ tailWord_2878347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878347).length < 2 ^ (prefixWord ++ tailWord_2878347).sum := by decide
  have hdescent : baseEnd_2878347 < baseStart_2878347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878377 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 6, 2]
def baseStart_2878377 : Nat := 118140960795 + 2878377 * 2 ^ 59
def prefixEnd_2878377 : Nat := 4983230072969 + 3 ^ 40 * 2878377 * 2
def baseEnd_2878377 : Nat := 1477990905846590070450091

theorem tailTrace_2878377 : CollatzResearch.WordTrace tailWord_2878377 prefixEnd_2878377 1477990905846590070450091 := by
  unfold tailWord_2878377
  simp only [CollatzResearch.WordTrace]
  refine ⟨104983033893139191499417385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69988689262092794332944923 104983033893139191499417385)
  ·
    refine ⟨78737275419854393624563039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104983033893139191499417385 78737275419854393624563039)
    ·
      refine ⟨118105913129781590436844559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78737275419854393624563039 118105913129781590436844559)
      ·
        refine ⟨177158869694672385655266839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118105913129781590436844559 177158869694672385655266839)
        ·
          refine ⟨265738304542008578482900259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177158869694672385655266839 265738304542008578482900259)
          ·
            refine ⟨398607456813012867724350389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265738304542008578482900259 398607456813012867724350389)
            ·
              refine ⟨37369449076219956349157849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398607456813012867724350389 37369449076219956349157849)
              ·
                refine ⟨28027086807164967261868387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37369449076219956349157849 28027086807164967261868387)
                ·
                  refine ⟨42040630210747450892802581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28027086807164967261868387 42040630210747450892802581)
                  ·
                    refine ⟨1970654541128786760600121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42040630210747450892802581 1970654541128786760600121)
                    ·
                      refine ⟨1477990905846590070450091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970654541128786760600121 1477990905846590070450091)
                      ·
                        rfl

theorem cell23_2878377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6, 2].length) (baseStart_2878377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878377 prefixEnd_2878377 := by exact prefixLift 2878377
  have htrace : WordTrace (prefixWord ++ tailWord_2878377) baseStart_2878377 baseEnd_2878377 := by
    simpa [prefixWord, tailWord_2878377, baseEnd_2878377] using wordTrace_append hprefix tailTrace_2878377
  have hstable : (prefixWord ++ tailWord_2878377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878377).length < 2 ^ (prefixWord ++ tailWord_2878377).sum := by decide
  have hdescent : baseEnd_2878377 < baseStart_2878377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878406 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2878406 : Nat := 118140960795 + 2878406 * 2 ^ 59
def prefixEnd_2878406 : Nat := 4983230072969 + 3 ^ 40 * 2878406 * 2
def baseEnd_2878406 : Nat := 1478005796785570456987459

theorem tailTrace_2878406 : CollatzResearch.WordTrace tailWord_2878406 prefixEnd_2878406 1478005796785570456987459 := by
  unfold tailWord_2878406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280752862813566545381971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69989394406689419634815381 3280752862813566545381971)
  ·
    refine ⟨4921129294220349818072957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280752862813566545381971 4921129294220349818072957)
    ·
      refine ⟨1845423485332631181777359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4921129294220349818072957 1845423485332631181777359)
      ·
        refine ⟨2768135227998946772666039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845423485332631181777359 2768135227998946772666039)
        ·
          refine ⟨4152202841998420158999059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768135227998946772666039 4152202841998420158999059)
          ·
            refine ⟨6228304262997630238498589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152202841998420158999059 6228304262997630238498589)
            ·
              refine ⟨2335614098624111339436971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6228304262997630238498589 2335614098624111339436971)
              ·
                refine ⟨3503421147936167009155457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335614098624111339436971 3503421147936167009155457)
                ·
                  refine ⟨2627565860952125256866593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503421147936167009155457 2627565860952125256866593)
                  ·
                    refine ⟨1970674395714093942649945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627565860952125256866593 1970674395714093942649945)
                    ·
                      refine ⟨1478005796785570456987459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970674395714093942649945 1478005796785570456987459)
                      ·
                        rfl

theorem cell23_2878406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2878406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878406 prefixEnd_2878406 := by exact prefixLift 2878406
  have htrace : WordTrace (prefixWord ++ tailWord_2878406) baseStart_2878406 baseEnd_2878406 := by
    simpa [prefixWord, tailWord_2878406, baseEnd_2878406] using wordTrace_append hprefix tailTrace_2878406
  have hstable : (prefixWord ++ tailWord_2878406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878406).length < 2 ^ (prefixWord ++ tailWord_2878406).sum := by decide
  have hdescent : baseEnd_2878406 < baseStart_2878406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878434 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_2878434 : Nat := 118140960795 + 2878434 * 2 ^ 59
def prefixEnd_2878434 : Nat := 4983230072969 + 3 ^ 40 * 2878434 * 2
def baseEnd_2878434 : Nat := 164224463804877371937481

theorem tailTrace_2878434 : CollatzResearch.WordTrace tailWord_2878434 prefixEnd_2878434 164224463804877371937481 := by
  unfold tailWord_2878434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26246278213483172558560589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69990075235955126822828237 26246278213483172558560589)
  ·
    refine ⟨9842354330056189709460221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26246278213483172558560589 9842354330056189709460221)
    ·
      refine ⟨3690882873771071141047583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9842354330056189709460221 3690882873771071141047583)
      ·
        refine ⟨5536324310656606711571375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690882873771071141047583 5536324310656606711571375)
        ·
          refine ⟨8304486465984910067357063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536324310656606711571375 8304486465984910067357063)
          ·
            refine ⟨12456729698977365101035595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8304486465984910067357063 12456729698977365101035595)
            ·
              refine ⟨18685094548466047651553393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12456729698977365101035595 18685094548466047651553393)
              ·
                refine ⟨14013820911349535738665045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18685094548466047651553393 14013820911349535738665045)
                ·
                  refine ⟨164224463804877371937481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14013820911349535738665045 164224463804877371937481)
                  ·
                    rfl

theorem cell23_2878434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_2878434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878434 prefixEnd_2878434 := by exact prefixLift 2878434
  have htrace : WordTrace (prefixWord ++ tailWord_2878434) baseStart_2878434 baseEnd_2878434 := by
    simpa [prefixWord, tailWord_2878434, baseEnd_2878434] using wordTrace_append hprefix tailTrace_2878434
  have hstable : (prefixWord ++ tailWord_2878434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878434).length < 2 ^ (prefixWord ++ tailWord_2878434).sum := by decide
  have hdescent : baseEnd_2878434 < baseStart_2878434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878501 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_2878501 : Nat := 118140960795 + 2878501 * 2 ^ 59
def prefixEnd_2878501 : Nat := 4983230072969 + 3 ^ 40 * 2878501 * 2
def baseEnd_2878501 : Nat := 1478054577447747585299521

theorem tailTrace_2878501 : CollatzResearch.WordTrace tailWord_2878501 prefixEnd_2878501 1478054577447747585299521 := by
  unfold tailWord_2878501
  simp only [CollatzResearch.WordTrace]
  refine ⟨104987556544689960676931357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69991704363126640451287571 104987556544689960676931357)
  ·
    refine ⟨39370333704258735253849259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104987556544689960676931357 39370333704258735253849259)
    ·
      refine ⟨59055500556388102880773889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39370333704258735253849259 59055500556388102880773889)
      ·
        refine ⟨44291625417291077160580417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59055500556388102880773889 44291625417291077160580417)
        ·
          refine ⟨33218719062968307870435313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44291625417291077160580417 33218719062968307870435313)
          ·
            refine ⟨24914039297226230902826485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33218719062968307870435313 24914039297226230902826485)
            ·
              refine ⟨2335691184114959147139983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24914039297226230902826485 2335691184114959147139983)
              ·
                refine ⟨3503536776172438720709975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335691184114959147139983 3503536776172438720709975)
                ·
                  refine ⟨5255305164258658081064963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503536776172438720709975 5255305164258658081064963)
                  ·
                    refine ⟨7882957746387987121597445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5255305164258658081064963 7882957746387987121597445)
                    ·
                      refine ⟨1478054577447747585299521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7882957746387987121597445 1478054577447747585299521)
                      ·
                        rfl

theorem cell23_2878501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_2878501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878501 prefixEnd_2878501 := by exact prefixLift 2878501
  have htrace : WordTrace (prefixWord ++ tailWord_2878501) baseStart_2878501 baseEnd_2878501 := by
    simpa [prefixWord, tailWord_2878501, baseEnd_2878501] using wordTrace_append hprefix tailTrace_2878501
  have hstable : (prefixWord ++ tailWord_2878501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878501).length < 2 ^ (prefixWord ++ tailWord_2878501).sum := by decide
  have hdescent : baseEnd_2878501 < baseStart_2878501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878524 : List Nat := [2, 2, 2, 2, 2, 4, 1, 8]
def baseStart_2878524 : Nat := 118140960795 + 2878524 * 2 ^ 59
def prefixEnd_2878524 : Nat := 4983230072969 + 3 ^ 40 * 2878524 * 2
def baseEnd_2878524 : Nat := 54743199537140777604145

theorem tailTrace_2878524 : CollatzResearch.WordTrace tailWord_2878524 prefixEnd_2878524 54743199537140777604145 := by
  unfold tailWord_2878524
  simp only [CollatzResearch.WordTrace]
  refine ⟨52494197711803317802509313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69992263615737757070012417 52494197711803317802509313)
  ·
    refine ⟨39370648283852488351881985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52494197711803317802509313 39370648283852488351881985)
    ·
      refine ⟨29527986212889366263911489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39370648283852488351881985 29527986212889366263911489)
      ·
        refine ⟨22145989659667024697933617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29527986212889366263911489 22145989659667024697933617)
        ·
          refine ⟨16609492244750268523450213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22145989659667024697933617 16609492244750268523450213)
          ·
            refine ⟨3114279795890675348146915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16609492244750268523450213 3114279795890675348146915)
            ·
              refine ⟨4671419693836013022220373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114279795890675348146915 4671419693836013022220373)
              ·
                refine ⟨54743199537140777604145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4671419693836013022220373 54743199537140777604145)
                ·
                  rfl

theorem cell23_2878524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 8].length) (baseStart_2878524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878524 prefixEnd_2878524 := by exact prefixLift 2878524
  have htrace : WordTrace (prefixWord ++ tailWord_2878524) baseStart_2878524 baseEnd_2878524 := by
    simpa [prefixWord, tailWord_2878524, baseEnd_2878524] using wordTrace_append hprefix tailTrace_2878524
  have hstable : (prefixWord ++ tailWord_2878524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878524).length < 2 ^ (prefixWord ++ tailWord_2878524).sum := by decide
  have hdescent : baseEnd_2878524 < baseStart_2878524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878541 : List Nat := [1, 6, 1, 1, 1, 3, 3, 7]
def baseStart_2878541 : Nat := 118140960795 + 2878541 * 2 ^ 59
def prefixEnd_2878541 : Nat := 4983230072969 + 3 ^ 40 * 2878541 * 2
def baseEnd_2878541 : Nat := 54743522839775089955531

theorem tailTrace_2878541 : CollatzResearch.WordTrace tailWord_2878541 prefixEnd_2878541 54743522839775089955531 := by
  unfold tailWord_2878541
  simp only [CollatzResearch.WordTrace]
  refine ⟨104989015464545047508387477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69992676976363365005591651 104989015464545047508387477)
  ·
    refine ⟨4921360099900549101955663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104989015464545047508387477 4921360099900549101955663)
    ·
      refine ⟨7382040149850823652933495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4921360099900549101955663 7382040149850823652933495)
      ·
        refine ⟨11073060224776235479400243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382040149850823652933495 11073060224776235479400243)
        ·
          refine ⟨16609590337164353219100365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073060224776235479400243 16609590337164353219100365)
          ·
            refine ⟨6228596376436632457162637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16609590337164353219100365 6228596376436632457162637)
            ·
              refine ⟨2335723641163737171435989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6228596376436632457162637 2335723641163737171435989)
              ·
                refine ⟨54743522839775089955531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2335723641163737171435989 54743522839775089955531)
                ·
                  rfl

theorem cell23_2878541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 7].length) (baseStart_2878541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878541 prefixEnd_2878541 := by exact prefixLift 2878541
  have htrace : WordTrace (prefixWord ++ tailWord_2878541) baseStart_2878541 baseEnd_2878541 := by
    simpa [prefixWord, tailWord_2878541, baseEnd_2878541] using wordTrace_append hprefix tailTrace_2878541
  have hstable : (prefixWord ++ tailWord_2878541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878541).length < 2 ^ (prefixWord ++ tailWord_2878541).sum := by decide
  have hdescent : baseEnd_2878541 < baseStart_2878541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878577 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2878577 : Nat := 118140960795 + 2878577 * 2 ^ 59
def prefixEnd_2878577 : Nat := 4983230072969 + 3 ^ 40 * 2878577 * 2
def baseEnd_2878577 : Nat := 1478093601977489287949171

theorem tailTrace_2878577 : CollatzResearch.WordTrace tailWord_2878577 prefixEnd_2878577 1478093601977489287949171 := by
  unfold tailWord_2878577
  simp only [CollatzResearch.WordTrace]
  refine ⟨104990328492414625656697985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69993552328276417104465323 104990328492414625656697985)
  ·
    refine ⟨78742746369310969242523489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104990328492414625656697985 78742746369310969242523489)
    ·
      refine ⟨59057059776983226931892617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78742746369310969242523489 59057059776983226931892617)
      ·
        refine ⟨44292794832737420198919463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59057059776983226931892617 44292794832737420198919463)
        ·
          refine ⟨66439192249106130298379195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44292794832737420198919463 66439192249106130298379195)
          ·
            refine ⟨99658788373659195447568793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66439192249106130298379195 99658788373659195447568793)
            ·
              refine ⟨74744091280244396585676595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99658788373659195447568793 74744091280244396585676595)
              ·
                refine ⟨112116136920366594878514893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74744091280244396585676595 112116136920366594878514893)
                ·
                  refine ⟨42043551345137473079443085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112116136920366594878514893 42043551345137473079443085)
                  ·
                    refine ⟨15766331754426552404791157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42043551345137473079443085 15766331754426552404791157)
                    ·
                      refine ⟨1478093601977489287949171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15766331754426552404791157 1478093601977489287949171)
                      ·
                        rfl

theorem cell23_2878577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2878577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878577 prefixEnd_2878577 := by exact prefixLift 2878577
  have htrace : WordTrace (prefixWord ++ tailWord_2878577) baseStart_2878577 baseEnd_2878577 := by
    simpa [prefixWord, tailWord_2878577, baseEnd_2878577] using wordTrace_append hprefix tailTrace_2878577
  have hstable : (prefixWord ++ tailWord_2878577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878577).length < 2 ^ (prefixWord ++ tailWord_2878577).sum := by decide
  have hdescent : baseEnd_2878577 < baseStart_2878577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878585 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 2, 1, 3]
def baseStart_2878585 : Nat := 118140960795 + 2878585 * 2 ^ 59
def prefixEnd_2878585 : Nat := 4983230072969 + 3 ^ 40 * 2878585 * 2
def baseEnd_2878585 : Nat := 1478097709822725256649135

theorem tailTrace_2878585 : CollatzResearch.WordTrace tailWord_2878585 prefixEnd_2878585 1478097709822725256649135 := by
  unfold tailWord_2878585
  simp only [CollatzResearch.WordTrace]
  refine ⟨104990620276385643022989209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69993746850923762015326139 104990620276385643022989209)
  ·
    refine ⟨78742965207289232267241907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104990620276385643022989209 78742965207289232267241907)
    ·
      refine ⟨118114447810933848400862861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78742965207289232267241907 118114447810933848400862861)
      ·
        refine ⟨44292917929100193150323573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118114447810933848400862861 44292917929100193150323573)
        ·
          refine ⟨4152461055853143107842835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44292917929100193150323573 4152461055853143107842835)
          ·
            refine ⟨6228691583779714661764253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152461055853143107842835 6228691583779714661764253)
            ·
              refine ⟨2335759343917392998161595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6228691583779714661764253 2335759343917392998161595)
              ·
                refine ⟨3503639015876089497242393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335759343917392998161595 3503639015876089497242393)
                ·
                  refine ⟨2627729261907067122931795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503639015876089497242393 2627729261907067122931795)
                  ·
                    refine ⟨3941593892860600684397693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627729261907067122931795 3941593892860600684397693)
                    ·
                      refine ⟨1478097709822725256649135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3941593892860600684397693 1478097709822725256649135)
                      ·
                        rfl

theorem cell23_2878585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_2878585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878585 prefixEnd_2878585 := by exact prefixLift 2878585
  have htrace : WordTrace (prefixWord ++ tailWord_2878585) baseStart_2878585 baseEnd_2878585 := by
    simpa [prefixWord, tailWord_2878585, baseEnd_2878585] using wordTrace_append hprefix tailTrace_2878585
  have hstable : (prefixWord ++ tailWord_2878585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878585).length < 2 ^ (prefixWord ++ tailWord_2878585).sum := by decide
  have hdescent : baseEnd_2878585 < baseStart_2878585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878617 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2878617 : Nat := 118140960795 + 2878617 * 2 ^ 59
def prefixEnd_2878617 : Nat := 4983230072969 + 3 ^ 40 * 2878617 * 2
def baseEnd_2878617 : Nat := 1478114141203669131448987

theorem tailTrace_2878617 : CollatzResearch.WordTrace tailWord_2878617 prefixEnd_2878617 1478114141203669131448987 := by
  unfold tailWord_2878617
  simp only [CollatzResearch.WordTrace]
  refine ⟨104991787412269712488154105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69994524941513141658769403 104991787412269712488154105)
  ·
    refine ⟨78743840559202284366115579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104991787412269712488154105 78743840559202284366115579)
    ·
      refine ⟨118115760838803426549173369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78743840559202284366115579 118115760838803426549173369)
      ·
        refine ⟨88586820629102569911880027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118115760838803426549173369 88586820629102569911880027)
        ·
          refine ⟨132880230943653854867820041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88586820629102569911880027 132880230943653854867820041)
          ·
            refine ⟨99660173207740391150865031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132880230943653854867820041 99660173207740391150865031)
            ·
              refine ⟨149490259811610586726297547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99660173207740391150865031 149490259811610586726297547)
              ·
                refine ⟨224235389717415880089446321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149490259811610586726297547 224235389717415880089446321)
                ·
                  refine ⟨168176542288061910067084741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224235389717415880089446321 168176542288061910067084741)
                  ·
                    refine ⟨31533101679011608137578389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168176542288061910067084741 31533101679011608137578389)
                    ·
                      refine ⟨1478114141203669131448987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31533101679011608137578389 1478114141203669131448987)
                      ·
                        rfl

theorem cell23_2878617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2878617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878617 prefixEnd_2878617 := by exact prefixLift 2878617
  have htrace : WordTrace (prefixWord ++ tailWord_2878617) baseStart_2878617 baseEnd_2878617 := by
    simpa [prefixWord, tailWord_2878617, baseEnd_2878617] using wordTrace_append hprefix tailTrace_2878617
  have hstable : (prefixWord ++ tailWord_2878617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878617).length < 2 ^ (prefixWord ++ tailWord_2878617).sum := by decide
  have hdescent : baseEnd_2878617 < baseStart_2878617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878631 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 7]
def baseStart_2878631 : Nat := 118140960795 + 2878631 * 2 ^ 59
def prefixEnd_2878631 : Nat := 4983230072969 + 3 ^ 40 * 2878631 * 2
def baseEnd_2878631 : Nat := 164235703325870230741547

theorem tailTrace_2878631 : CollatzResearch.WordTrace tailWord_2878631 prefixEnd_2878631 164235703325870230741547 := by
  unfold tailWord_2878631
  simp only [CollatzResearch.WordTrace]
  refine ⟨104992298034218992879163747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69994865356145995252775831 104992298034218992879163747)
  ·
    refine ⟨157488447051328489318745621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104992298034218992879163747 157488447051328489318745621)
    ·
      refine ⟨7382270955531022936816201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157488447051328489318745621 7382270955531022936816201)
      ·
        refine ⟨5536703216648267202612151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7382270955531022936816201 5536703216648267202612151)
        ·
          refine ⟨8305054824972400803918227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536703216648267202612151 8305054824972400803918227)
          ·
            refine ⟨12457582237458601205877341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8305054824972400803918227 12457582237458601205877341)
            ·
              refine ⟨4671593339046975452204003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12457582237458601205877341 4671593339046975452204003)
              ·
                refine ⟨7007390008570463178306005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671593339046975452204003 7007390008570463178306005)
                ·
                  refine ⟨164235703325870230741547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7007390008570463178306005 164235703325870230741547)
                  ·
                    rfl

theorem cell23_2878631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 7].length) (baseStart_2878631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878631 prefixEnd_2878631 := by exact prefixLift 2878631
  have htrace : WordTrace (prefixWord ++ tailWord_2878631) baseStart_2878631 baseEnd_2878631 := by
    simpa [prefixWord, tailWord_2878631, baseEnd_2878631] using wordTrace_append hprefix tailTrace_2878631
  have hstable : (prefixWord ++ tailWord_2878631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878631).length < 2 ^ (prefixWord ++ tailWord_2878631).sum := by decide
  have hdescent : baseEnd_2878631 < baseStart_2878631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878642 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_2878642 : Nat := 118140960795 + 2878642 * 2 ^ 59
def prefixEnd_2878642 : Nat := 4983230072969 + 3 ^ 40 * 2878642 * 2
def baseEnd_2878642 : Nat := 1478126978220031533636373

theorem tailTrace_2878642 : CollatzResearch.WordTrace tailWord_2878642 prefixEnd_2878642 1478126978220031533636373 := by
  unfold tailWord_2878642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26248174809294785439453545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69995132824786094505209453 26248174809294785439453545)
  ·
    refine ⟨19686131106971089079590159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26248174809294785439453545 19686131106971089079590159)
    ·
      refine ⟨29529196660456633619385239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19686131106971089079590159 29529196660456633619385239)
      ·
        refine ⟨44293794990684950429077859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29529196660456633619385239 44293794990684950429077859)
        ·
          refine ⟨66440692486027425643616789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44293794990684950429077859 66440692486027425643616789)
          ·
            refine ⟨3114407460282535577044537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66440692486027425643616789 3114407460282535577044537)
            ·
              refine ⟨2335805595211901682783403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3114407460282535577044537 2335805595211901682783403)
              ·
                refine ⟨3503708392817852524175105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335805595211901682783403 3503708392817852524175105)
                ·
                  refine ⟨2627781294613389393131329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503708392817852524175105 2627781294613389393131329)
                  ·
                    refine ⟨1970835970960042044848497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627781294613389393131329 1970835970960042044848497)
                    ·
                      refine ⟨1478126978220031533636373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970835970960042044848497 1478126978220031533636373)
                      ·
                        rfl

theorem cell23_2878642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_2878642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878642 prefixEnd_2878642 := by exact prefixLift 2878642
  have htrace : WordTrace (prefixWord ++ tailWord_2878642) baseStart_2878642 baseEnd_2878642 := by
    simpa [prefixWord, tailWord_2878642, baseEnd_2878642] using wordTrace_append hprefix tailTrace_2878642
  have hstable : (prefixWord ++ tailWord_2878642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878642).length < 2 ^ (prefixWord ++ tailWord_2878642).sum := by decide
  have hdescent : baseEnd_2878642 < baseStart_2878642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878646 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2878646 : Nat := 118140960795 + 2878646 * 2 ^ 59
def prefixEnd_2878646 : Nat := 4983230072969 + 3 ^ 40 * 2878646 * 2
def baseEnd_2878646 : Nat := 1478129032142649517986355

theorem tailTrace_2878646 : CollatzResearch.WordTrace tailWord_2878646 prefixEnd_2878646 1478129032142649517986355 := by
  unfold tailWord_2878646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6562052820572790652559987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69995230086109766960639861 6562052820572790652559987)
  ·
    refine ⟨9843079230859185978839981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6562052820572790652559987 9843079230859185978839981)
    ·
      refine ⟨3691154711572194742064993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9843079230859185978839981 3691154711572194742064993)
      ·
        refine ⟨2768366033679146056548745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3691154711572194742064993 2768366033679146056548745)
        ·
          refine ⟨2076274525259359542411559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2768366033679146056548745 2076274525259359542411559)
          ·
            refine ⟨3114411787889039313617339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076274525259359542411559 3114411787889039313617339)
            ·
              refine ⟨4671617681833558970426009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114411787889039313617339 4671617681833558970426009)
              ·
                refine ⟨3503713261375169227819507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4671617681833558970426009 3503713261375169227819507)
                ·
                  refine ⟨5255569892062753841729261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503713261375169227819507 5255569892062753841729261)
                  ·
                    refine ⟨1970838709523532690648473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5255569892062753841729261 1970838709523532690648473)
                    ·
                      refine ⟨1478129032142649517986355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970838709523532690648473 1478129032142649517986355)
                      ·
                        rfl

theorem cell23_2878646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2878646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878646 prefixEnd_2878646 := by exact prefixLift 2878646
  have htrace : WordTrace (prefixWord ++ tailWord_2878646) baseStart_2878646 baseEnd_2878646 := by
    simpa [prefixWord, tailWord_2878646, baseEnd_2878646] using wordTrace_append hprefix tailTrace_2878646
  have hstable : (prefixWord ++ tailWord_2878646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878646).length < 2 ^ (prefixWord ++ tailWord_2878646).sum := by decide
  have hdescent : baseEnd_2878646 < baseStart_2878646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878664 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2878664 : Nat := 118140960795 + 2878664 * 2 ^ 59
def prefixEnd_2878664 : Nat := 4983230072969 + 3 ^ 40 * 2878664 * 2
def baseEnd_2878664 : Nat := 1478138274794430447561271

theorem tailTrace_2878664 : CollatzResearch.WordTrace tailWord_2878664 prefixEnd_2878664 1478138274794430447561271 := by
  unfold tailWord_2878664
  simp only [CollatzResearch.WordTrace]
  refine ⟨52496750821549719757557523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69995667762066293010076697 52496750821549719757557523)
  ·
    refine ⟨78745126232324579636336285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52496750821549719757557523 78745126232324579636336285)
    ·
      refine ⟨29529422337121717363626107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78745126232324579636336285 29529422337121717363626107)
      ·
        refine ⟨44294133505682576045439161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29529422337121717363626107 44294133505682576045439161)
        ·
          refine ⟨33220600129261932034079371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44294133505682576045439161 33220600129261932034079371)
          ·
            refine ⟨49830900193892898051119057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33220600129261932034079371 49830900193892898051119057)
            ·
              refine ⟨37373175145419673538339293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49830900193892898051119057 37373175145419673538339293)
              ·
                refine ⟨14014940679532377576877235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37373175145419673538339293 14014940679532377576877235)
                ·
                  refine ⟨21022411019298566365315853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14014940679532377576877235 21022411019298566365315853)
                  ·
                    refine ⟨7883404132236962386993445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21022411019298566365315853 7883404132236962386993445)
                    ·
                      refine ⟨1478138274794430447561271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7883404132236962386993445 1478138274794430447561271)
                      ·
                        rfl

theorem cell23_2878664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2878664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878664 prefixEnd_2878664 := by exact prefixLift 2878664
  have htrace : WordTrace (prefixWord ++ tailWord_2878664) baseStart_2878664 baseEnd_2878664 := by
    simpa [prefixWord, tailWord_2878664, baseEnd_2878664] using wordTrace_append hprefix tailTrace_2878664
  have hstable : (prefixWord ++ tailWord_2878664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878664).length < 2 ^ (prefixWord ++ tailWord_2878664).sum := by decide
  have hdescent : baseEnd_2878664 < baseStart_2878664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878681 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 2, 4, 2]
def baseStart_2878681 : Nat := 118140960795 + 2878681 * 2 ^ 59
def prefixEnd_2878681 : Nat := 4983230072969 + 3 ^ 40 * 2878681 * 2
def baseEnd_2878681 : Nat := 1478147003965556881048693

theorem tailTrace_2878681 : CollatzResearch.WordTrace tailWord_2878681 prefixEnd_2878681 1478147003965556881048693 := by
  unfold tailWord_2878681
  simp only [CollatzResearch.WordTrace]
  refine ⟨104994121684037851418483897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69996081122691900945655931 104994121684037851418483897)
  ·
    refine ⟨78745591263028388563862923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104994121684037851418483897 78745591263028388563862923)
    ·
      refine ⟨118118386894542582845794385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78745591263028388563862923 118118386894542582845794385)
      ·
        refine ⟨88588790170906937134345789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118118386894542582845794385 88588790170906937134345789)
        ·
          refine ⟨33220796314090101425379671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88588790170906937134345789 33220796314090101425379671)
          ·
            refine ⟨49831194471135152138069507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33220796314090101425379671 49831194471135152138069507)
            ·
              refine ⟨74746791706702728207104261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49831194471135152138069507 74746791706702728207104261)
              ·
                refine ⟨14015023445006761538832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74746791706702728207104261 14015023445006761538832049)
                ·
                  refine ⟨10511267583755071154124037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14015023445006761538832049 10511267583755071154124037)
                  ·
                    refine ⟨1970862671954075841398257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10511267583755071154124037 1970862671954075841398257)
                    ·
                      refine ⟨1478147003965556881048693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970862671954075841398257 1478147003965556881048693)
                      ·
                        rfl

theorem cell23_2878681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_2878681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878681 prefixEnd_2878681 := by exact prefixLift 2878681
  have htrace : WordTrace (prefixWord ++ tailWord_2878681) baseStart_2878681 baseEnd_2878681 := by
    simpa [prefixWord, tailWord_2878681, baseEnd_2878681] using wordTrace_append hprefix tailTrace_2878681
  have hstable : (prefixWord ++ tailWord_2878681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878681).length < 2 ^ (prefixWord ++ tailWord_2878681).sum := by decide
  have hdescent : baseEnd_2878681 < baseStart_2878681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878698 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_2878698 : Nat := 118140960795 + 2878698 * 2 ^ 59
def prefixEnd_2878698 : Nat := 4983230072969 + 3 ^ 40 * 2878698 * 2
def baseEnd_2878698 : Nat := 1478155733136683314536115

theorem tailTrace_2878698 : CollatzResearch.WordTrace tailWord_2878698 prefixEnd_2878698 1478155733136683314536115 := by
  unfold tailWord_2878698
  simp only [CollatzResearch.WordTrace]
  refine ⟨26248685431244065830463187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69996494483317508881235165 26248685431244065830463187)
  ·
    refine ⟨39373028146866098745694781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26248685431244065830463187 39373028146866098745694781)
    ·
      refine ⟨14764885555074787029635543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39373028146866098745694781 14764885555074787029635543)
      ·
        refine ⟨22147328332612180544453315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14764885555074787029635543 22147328332612180544453315)
        ·
          refine ⟨33220992498918270816679973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22147328332612180544453315 33220992498918270816679973)
          ·
            refine ⟨6228936093547175778127495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33220992498918270816679973 6228936093547175778127495)
            ·
              refine ⟨9343404140320763667191243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228936093547175778127495 9343404140320763667191243)
              ·
                refine ⟨14015106210481145500786865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9343404140320763667191243 14015106210481145500786865)
                ·
                  refine ⟨10511329657860859125590149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14015106210481145500786865 10511329657860859125590149)
                  ·
                    refine ⟨1970874310848911086048153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10511329657860859125590149 1970874310848911086048153)
                    ·
                      refine ⟨1478155733136683314536115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970874310848911086048153 1478155733136683314536115)
                      ·
                        rfl

theorem cell23_2878698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_2878698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878698 prefixEnd_2878698 := by exact prefixLift 2878698
  have htrace : WordTrace (prefixWord ++ tailWord_2878698) baseStart_2878698 baseEnd_2878698 := by
    simpa [prefixWord, tailWord_2878698, baseEnd_2878698] using wordTrace_append hprefix tailTrace_2878698
  have hstable : (prefixWord ++ tailWord_2878698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878698).length < 2 ^ (prefixWord ++ tailWord_2878698).sum := by decide
  have hdescent : baseEnd_2878698 < baseStart_2878698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878718 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2878718 : Nat := 118140960795 + 2878718 * 2 ^ 59
def prefixEnd_2878718 : Nat := 4983230072969 + 3 ^ 40 * 2878718 * 2
def baseEnd_2878718 : Nat := 1478166002749773236286023

theorem tailTrace_2878718 : CollatzResearch.WordTrace tailWord_2878718 prefixEnd_2878718 1478166002749773236286023 := by
  unfold tailWord_2878718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13124433898112975842197601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69996980789935871158387205 13124433898112975842197601)
  ·
    refine ⟨9843325423584731881648201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13124433898112975842197601 9843325423584731881648201)
    ·
      refine ⟨7382494067688548911236151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9843325423584731881648201 7382494067688548911236151)
      ·
        refine ⟨11073741101532823366854227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382494067688548911236151 11073741101532823366854227)
        ·
          refine ⟨16610611652299235050281341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11073741101532823366854227 16610611652299235050281341)
          ·
            refine ⟨6228979369612213143855503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16610611652299235050281341 6228979369612213143855503)
            ·
              refine ⟨9343469054418319715783255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228979369612213143855503 9343469054418319715783255)
              ·
                refine ⟨14015203581627479573674883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9343469054418319715783255 14015203581627479573674883)
                ·
                  refine ⟨21022805372441219360512325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14015203581627479573674883 21022805372441219360512325)
                  ·
                    refine ⟨3941776007332728630096061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21022805372441219360512325 3941776007332728630096061)
                    ·
                      refine ⟨1478166002749773236286023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3941776007332728630096061 1478166002749773236286023)
                      ·
                        rfl

theorem cell23_2878718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2878718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878718 prefixEnd_2878718 := by exact prefixLift 2878718
  have htrace : WordTrace (prefixWord ++ tailWord_2878718) baseStart_2878718 baseEnd_2878718 := by
    simpa [prefixWord, tailWord_2878718, baseEnd_2878718] using wordTrace_append hprefix tailTrace_2878718
  have hstable : (prefixWord ++ tailWord_2878718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878718).length < 2 ^ (prefixWord ++ tailWord_2878718).sum := by decide
  have hdescent : baseEnd_2878718 < baseStart_2878718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878748 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2878748 : Nat := 118140960795 + 2878748 * 2 ^ 59
def prefixEnd_2878748 : Nat := 4983230072969 + 3 ^ 40 * 2878748 * 2
def baseEnd_2878748 : Nat := 1478181407169408118910885

theorem tailTrace_2878748 : CollatzResearch.WordTrace tailWord_2878748 prefixEnd_2878748 1478181407169408118910885 := by
  unfold tailWord_2878748
  simp only [CollatzResearch.WordTrace]
  refine ⟨52498282687397560930586449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69997710249863414574115265 52498282687397560930586449)
  ·
    refine ⟨39373712015548170697939837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52498282687397560930586449 39373712015548170697939837)
    ·
      refine ⟨14765142005830564011727439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39373712015548170697939837 14765142005830564011727439)
      ·
        refine ⟨22147713008745846017591159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14765142005830564011727439 22147713008745846017591159)
        ·
          refine ⟨33221569513118769026386739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22147713008745846017591159 33221569513118769026386739)
          ·
            refine ⟨49832354269678153539580109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33221569513118769026386739 49832354269678153539580109)
            ·
              refine ⟨18687132851129307577342541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49832354269678153539580109 18687132851129307577342541)
              ·
                refine ⟨7007674819173490341503453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18687132851129307577342541 7007674819173490341503453)
                ·
                  refine ⟨2627878057190058878063795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7007674819173490341503453 2627878057190058878063795)
                  ·
                    refine ⟨3941817085785088317095693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627878057190058878063795 3941817085785088317095693)
                    ·
                      refine ⟨1478181407169408118910885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3941817085785088317095693 1478181407169408118910885)
                      ·
                        rfl

theorem cell23_2878748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2878748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878748 prefixEnd_2878748 := by exact prefixLift 2878748
  have htrace : WordTrace (prefixWord ++ tailWord_2878748) baseStart_2878748 baseEnd_2878748 := by
    simpa [prefixWord, tailWord_2878748, baseEnd_2878748] using wordTrace_append hprefix tailTrace_2878748
  have hstable : (prefixWord ++ tailWord_2878748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878748).length < 2 ^ (prefixWord ++ tailWord_2878748).sum := by decide
  have hdescent : baseEnd_2878748 < baseStart_2878748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878791 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2878791 : Nat := 118140960795 + 2878791 * 2 ^ 59
def prefixEnd_2878791 : Nat := 4983230072969 + 3 ^ 40 * 2878791 * 2
def baseEnd_2878791 : Nat := 1478203486837551450673187

theorem tailTrace_2878791 : CollatzResearch.WordTrace tailWord_2878791 prefixEnd_2878791 1478203486837551450673187 := by
  unfold tailWord_2878791
  simp only [CollatzResearch.WordTrace]
  refine ⟨104998133713639340204988227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69998755809092893469992151 104998133713639340204988227)
  ·
    refine ⟨157497200570459010307482341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104998133713639340204988227 157497200570459010307482341)
    ·
      refine ⟨29530725106961064432652939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157497200570459010307482341 29530725106961064432652939)
      ·
        refine ⟨44296087660441596648979409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29530725106961064432652939 44296087660441596648979409)
        ·
          refine ⟨33222065745331197486734557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44296087660441596648979409 33222065745331197486734557)
          ·
            refine ⟨12458274654499199057525459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33222065745331197486734557 12458274654499199057525459)
            ·
              refine ⟨18687411981748798586288189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12458274654499199057525459 18687411981748798586288189)
              ·
                refine ⟨7007779493155799469858071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18687411981748798586288189 7007779493155799469858071)
                ·
                  refine ⟨10511669239733699204787107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7007779493155799469858071 10511669239733699204787107)
                  ·
                    refine ⟨15767503859600548807180661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10511669239733699204787107 15767503859600548807180661)
                    ·
                      refine ⟨1478203486837551450673187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15767503859600548807180661 1478203486837551450673187)
                      ·
                        rfl

theorem cell23_2878791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2878791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878791 prefixEnd_2878791 := by exact prefixLift 2878791
  have htrace : WordTrace (prefixWord ++ tailWord_2878791) baseStart_2878791 baseEnd_2878791 := by
    simpa [prefixWord, tailWord_2878791, baseEnd_2878791] using wordTrace_append hprefix tailTrace_2878791
  have hstable : (prefixWord ++ tailWord_2878791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878791).length < 2 ^ (prefixWord ++ tailWord_2878791).sum := by decide
  have hdescent : baseEnd_2878791 < baseStart_2878791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878798 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_2878798 : Nat := 118140960795 + 2878798 * 2 ^ 59
def prefixEnd_2878798 : Nat := 4983230072969 + 3 ^ 40 * 2878798 * 2
def baseEnd_2878798 : Nat := 492735693734044307761885

theorem tailTrace_2878798 : CollatzResearch.WordTrace tailWord_2878798 prefixEnd_2878798 492735693734044307761885 := by
  unfold tailWord_2878798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13124798628076747550061631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69998926016409320266995365 13124798628076747550061631)
  ·
    refine ⟨19687197942115121325092447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13124798628076747550061631 19687197942115121325092447)
    ·
      refine ⟨29530796913172681987638671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19687197942115121325092447 29530796913172681987638671)
      ·
        refine ⟨44296195369759022981458007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29530796913172681987638671 44296195369759022981458007)
        ·
          refine ⟨66444293054638534472187011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44296195369759022981458007 66444293054638534472187011)
          ·
            refine ⟨99666439581957801708280517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66444293054638534472187011 99666439581957801708280517)
            ·
              refine ⟨18687457421617087820302597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99666439581957801708280517 18687457421617087820302597)
              ·
                refine ⟨3503898266553203966306737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18687457421617087820302597 3503898266553203966306737)
                ·
                  refine ⟨2627923699914902974730053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503898266553203966306737 2627923699914902974730053)
                  ·
                    refine ⟨492735693734044307761885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2627923699914902974730053 492735693734044307761885)
                    ·
                      rfl

theorem cell23_2878798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_2878798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878798 prefixEnd_2878798 := by exact prefixLift 2878798
  have htrace : WordTrace (prefixWord ++ tailWord_2878798) baseStart_2878798 baseEnd_2878798 := by
    simpa [prefixWord, tailWord_2878798, baseEnd_2878798] using wordTrace_append hprefix tailTrace_2878798
  have hstable : (prefixWord ++ tailWord_2878798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878798).length < 2 ^ (prefixWord ++ tailWord_2878798).sum := by decide
  have hdescent : baseEnd_2878798 < baseStart_2878798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878806 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2878806 : Nat := 118140960795 + 2878806 * 2 ^ 59
def prefixEnd_2878806 : Nat := 4983230072969 + 3 ^ 40 * 2878806 * 2
def baseEnd_2878806 : Nat := 164245687671929876887291

theorem tailTrace_2878806 : CollatzResearch.WordTrace tailWord_2878806 prefixEnd_2878806 164245687671929876887291 := by
  unfold tailWord_2878806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6562417550536562360424017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69999120539056665177856181 6562417550536562360424017)
  ·
    refine ⟨4921813162902421770318013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6562417550536562360424017 4921813162902421770318013)
    ·
      refine ⟨1845679936088408163869255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4921813162902421770318013 1845679936088408163869255)
      ·
        refine ⟨2768519904132612245803883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845679936088408163869255 2768519904132612245803883)
        ·
          refine ⟨4152779856198918368705825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768519904132612245803883 4152779856198918368705825)
          ·
            refine ⟨3114584892149188776529369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4152779856198918368705825 3114584892149188776529369)
            ·
              refine ⟨2335938669111891582397027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3114584892149188776529369 2335938669111891582397027)
              ·
                refine ⟨3503908003667837373595541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335938669111891582397027 3503908003667837373595541)
                ·
                  refine ⟨164245687671929876887291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3503908003667837373595541 164245687671929876887291)
                  ·
                    rfl

theorem cell23_2878806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2878806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878806 prefixEnd_2878806 := by exact prefixLift 2878806
  have htrace : WordTrace (prefixWord ++ tailWord_2878806) baseStart_2878806 baseEnd_2878806 := by
    simpa [prefixWord, tailWord_2878806, baseEnd_2878806] using wordTrace_append hprefix tailTrace_2878806
  have hstable : (prefixWord ++ tailWord_2878806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878806).length < 2 ^ (prefixWord ++ tailWord_2878806).sum := by decide
  have hdescent : baseEnd_2878806 < baseStart_2878806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878818 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2878818 : Nat := 118140960795 + 2878818 * 2 ^ 59
def prefixEnd_2878818 : Nat := 4983230072969 + 3 ^ 40 * 2878818 * 2
def baseEnd_2878818 : Nat := 1478217350815222845035563

theorem tailTrace_2878818 : CollatzResearch.WordTrace tailWord_2878818 prefixEnd_2878818 1478217350815222845035563 := by
  unfold tailWord_2878818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249779621135380954055277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69999412323027682544147405 26249779621135380954055277)
  ·
    refine ⟨9843667357925767857770729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26249779621135380954055277 9843667357925767857770729)
    ·
      refine ⟨7382750518444325893328047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9843667357925767857770729 7382750518444325893328047)
      ·
        refine ⟨11074125777666488839992071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382750518444325893328047 11074125777666488839992071)
        ·
          refine ⟨16611188666499733259988107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074125777666488839992071 16611188666499733259988107)
          ·
            refine ⟨24916782999749599889982161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611188666499733259988107 24916782999749599889982161)
            ·
              refine ⟨18687587249812199917486621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24916782999749599889982161 18687587249812199917486621)
              ·
                refine ⟨7007845218679574969057483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18687587249812199917486621 7007845218679574969057483)
                ·
                  refine ⟨10511767828019362453586225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7007845218679574969057483 10511767828019362453586225)
                  ·
                    refine ⟨7883825871014521840189669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10511767828019362453586225 7883825871014521840189669)
                    ·
                      refine ⟨1478217350815222845035563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7883825871014521840189669 1478217350815222845035563)
                      ·
                        rfl

theorem cell23_2878818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2878818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878818 prefixEnd_2878818 := by exact prefixLift 2878818
  have htrace : WordTrace (prefixWord ++ tailWord_2878818) baseStart_2878818 baseEnd_2878818 := by
    simpa [prefixWord, tailWord_2878818, baseEnd_2878818] using wordTrace_append hprefix tailTrace_2878818
  have hstable : (prefixWord ++ tailWord_2878818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878818).length < 2 ^ (prefixWord ++ tailWord_2878818).sum := by decide
  have hdescent : baseEnd_2878818 < baseStart_2878818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878855 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2878855 : Nat := 118140960795 + 2878855 * 2 ^ 59
def prefixEnd_2878855 : Nat := 4983230072969 + 3 ^ 40 * 2878855 * 2
def baseEnd_2878855 : Nat := 1478236349599439200272893

theorem tailTrace_2878855 : CollatzResearch.WordTrace tailWord_2878855 prefixEnd_2878855 1478236349599439200272893 := by
  unfold tailWord_2878855
  simp only [CollatzResearch.WordTrace]
  refine ⟨105000467985407479135318019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70000311990271652756878679 105000467985407479135318019)
  ·
    refine ⟨157500701978111218702977029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105000467985407479135318019 157500701978111218702977029)
    ·
      refine ⟨29531381620895853506808193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157500701978111218702977029 29531381620895853506808193)
      ·
        refine ⟨22148536215671890130106145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29531381620895853506808193 22148536215671890130106145)
        ·
          refine ⟨16611402161753917597579609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22148536215671890130106145 16611402161753917597579609)
          ·
            refine ⟨12458551621315438198184707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16611402161753917597579609 12458551621315438198184707)
            ·
              refine ⟨18687827431973157297277061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12458551621315438198184707 18687827431973157297277061)
              ·
                refine ⟨3503967643494966993239449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18687827431973157297277061 3503967643494966993239449)
                ·
                  refine ⟨2627975732621225244929587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503967643494966993239449 2627975732621225244929587)
                  ·
                    refine ⟨3941963598931837867394381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2627975732621225244929587 3941963598931837867394381)
                    ·
                      refine ⟨1478236349599439200272893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3941963598931837867394381 1478236349599439200272893)
                      ·
                        rfl

theorem cell23_2878855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2878855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878855 prefixEnd_2878855 := by exact prefixLift 2878855
  have htrace : WordTrace (prefixWord ++ tailWord_2878855) baseStart_2878855 baseEnd_2878855 := by
    simpa [prefixWord, tailWord_2878855, baseEnd_2878855] using wordTrace_append hprefix tailTrace_2878855
  have hstable : (prefixWord ++ tailWord_2878855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878855).length < 2 ^ (prefixWord ++ tailWord_2878855).sum := by decide
  have hdescent : baseEnd_2878855 < baseStart_2878855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878856 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2878856 : Nat := 118140960795 + 2878856 * 2 ^ 59
def prefixEnd_2878856 : Nat := 4983230072969 + 3 ^ 40 * 2878856 * 2
def baseEnd_2878856 : Nat := 1478236863080093696360389

theorem tailTrace_2878856 : CollatzResearch.WordTrace tailWord_2878856 prefixEnd_2878856 1478236863080093696360389 := by
  unfold tailWord_2878856
  simp only [CollatzResearch.WordTrace]
  refine ⟨52500252229201928153052211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70000336305602570870736281 52500252229201928153052211)
  ·
    refine ⟨78750378343802892229578317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52500252229201928153052211 78750378343802892229578317)
    ·
      refine ⟨29531391878926084586091869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78750378343802892229578317 29531391878926084586091869)
      ·
        refine ⟨11074271954597281719784451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29531391878926084586091869 11074271954597281719784451)
        ·
          refine ⟨16611407931895922579676677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074271954597281719784451 16611407931895922579676677)
          ·
            refine ⟨3114638987230485483689377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16611407931895922579676677 3114638987230485483689377)
            ·
              refine ⟨2335979240422864112767033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3114638987230485483689377 2335979240422864112767033)
              ·
                refine ⟨1751984430317148084575275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335979240422864112767033 1751984430317148084575275)
                ·
                  refine ⟨2627976645475722126862913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751984430317148084575275 2627976645475722126862913)
                  ·
                    refine ⟨1970982484106791595147185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2627976645475722126862913 1970982484106791595147185)
                    ·
                      refine ⟨1478236863080093696360389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1970982484106791595147185 1478236863080093696360389)
                      ·
                        rfl

theorem cell23_2878856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2878856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878856 prefixEnd_2878856 := by exact prefixLift 2878856
  have htrace : WordTrace (prefixWord ++ tailWord_2878856) baseStart_2878856 baseEnd_2878856 := by
    simpa [prefixWord, tailWord_2878856, baseEnd_2878856] using wordTrace_append hprefix tailTrace_2878856
  have hstable : (prefixWord ++ tailWord_2878856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878856).length < 2 ^ (prefixWord ++ tailWord_2878856).sum := by decide
  have hdescent : baseEnd_2878856 < baseStart_2878856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878912 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2]
def baseStart_2878912 : Nat := 118140960795 + 2878912 * 2 ^ 59
def prefixEnd_2878912 : Nat := 4983230072969 + 3 ^ 40 * 2878912 * 2
def baseEnd_2878912 : Nat := 1478265617996745477260131

theorem tailTrace_2878912 : CollatzResearch.WordTrace tailWord_2878912 prefixEnd_2878912 1478265617996745477260131 := by
  unfold tailWord_2878912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52501273473100488935071495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70001697964133985246761993 52501273473100488935071495)
  ·
    refine ⟨78751910209650733402607243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52501273473100488935071495 78751910209650733402607243)
    ·
      refine ⟨118127865314476100103910865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78751910209650733402607243 118127865314476100103910865)
      ·
        refine ⟨88595898985857075077933149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118127865314476100103910865 88595898985857075077933149)
        ·
          refine ⟨33223462119696403154224931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88595898985857075077933149 33223462119696403154224931)
          ·
            refine ⟨49835193179544604731337397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33223462119696403154224931 49835193179544604731337397)
            ·
              refine ⟨4672049360582306693562881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49835193179544604731337397 4672049360582306693562881)
              ·
                refine ⟨3504037020436730020172161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4672049360582306693562881 3504037020436730020172161)
                ·
                  refine ⟨2628027765327547515129121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3504037020436730020172161 2628027765327547515129121)
                  ·
                    refine ⟨1971020823995660636346841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2628027765327547515129121 1971020823995660636346841)
                    ·
                      refine ⟨1478265617996745477260131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971020823995660636346841 1478265617996745477260131)
                      ·
                        rfl

theorem cell23_2878912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_2878912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878912 prefixEnd_2878912 := by exact prefixLift 2878912
  have htrace : WordTrace (prefixWord ++ tailWord_2878912) baseStart_2878912 baseEnd_2878912 := by
    simpa [prefixWord, tailWord_2878912, baseEnd_2878912] using wordTrace_append hprefix tailTrace_2878912
  have hstable : (prefixWord ++ tailWord_2878912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878912).length < 2 ^ (prefixWord ++ tailWord_2878912).sum := by decide
  have hdescent : baseEnd_2878912 < baseStart_2878912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878958 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2878958 : Nat := 118140960795 + 2878958 * 2 ^ 59
def prefixEnd_2878958 : Nat := 4983230072969 + 3 ^ 40 * 2878958 * 2
def baseEnd_2878958 : Nat := 1478289238106852297284919

theorem tailTrace_2878958 : CollatzResearch.WordTrace tailWord_2878958 prefixEnd_2878958 1478289238106852297284919 := by
  unfold tailWord_2878958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125528088004290965789691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70002816469356218484211685 13125528088004290965789691)
  ·
    refine ⟨19688292132006436448684537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13125528088004290965789691 19688292132006436448684537)
    ·
      refine ⟨14766219099004827336513403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19688292132006436448684537 14766219099004827336513403)
      ·
        refine ⟨22149328648507241004770105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14766219099004827336513403 22149328648507241004770105)
        ·
          refine ⟨16611996486380430753577579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22149328648507241004770105 16611996486380430753577579)
          ·
            refine ⟨24917994729570646130366369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611996486380430753577579 24917994729570646130366369)
            ·
              refine ⟨18688496047177984597774777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24917994729570646130366369 18688496047177984597774777)
              ·
                refine ⟨14016372035383488448331083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18688496047177984597774777 14016372035383488448331083)
                ·
                  refine ⟨21024558053075232672496625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14016372035383488448331083 21024558053075232672496625)
                  ·
                    refine ⟨15768418539806424504372469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21024558053075232672496625 15768418539806424504372469)
                    ·
                      refine ⟨1478289238106852297284919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15768418539806424504372469 1478289238106852297284919)
                      ·
                        rfl

theorem cell23_2878958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2878958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878958 prefixEnd_2878958 := by exact prefixLift 2878958
  have htrace : WordTrace (prefixWord ++ tailWord_2878958) baseStart_2878958 baseEnd_2878958 := by
    simpa [prefixWord, tailWord_2878958, baseEnd_2878958] using wordTrace_append hprefix tailTrace_2878958
  have hstable : (prefixWord ++ tailWord_2878958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878958).length < 2 ^ (prefixWord ++ tailWord_2878958).sum := by decide
  have hdescent : baseEnd_2878958 < baseStart_2878958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878965 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2878965 : Nat := 118140960795 + 2878965 * 2 ^ 59
def prefixEnd_2878965 : Nat := 4983230072969 + 3 ^ 40 * 2878965 * 2
def baseEnd_2878965 : Nat := 492764277490477923299129

theorem tailTrace_2878965 : CollatzResearch.WordTrace tailWord_2878965 prefixEnd_2878965 492764277490477923299129 := by
  unfold tailWord_2878965
  simp only [CollatzResearch.WordTrace]
  refine ⟨105004480015008967921822349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70002986676672645281214899 105004480015008967921822349)
  ·
    refine ⟨39376680005628362970683381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105004480015008967921822349 39376680005628362970683381)
    ·
      refine ⟨3691563750527659028501567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39376680005628362970683381 3691563750527659028501567)
      ·
        refine ⟨5537345625791488542752351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691563750527659028501567 5537345625791488542752351)
        ·
          refine ⟨8306018438687232814128527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537345625791488542752351 8306018438687232814128527)
          ·
            refine ⟨12459027658030849221192791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306018438687232814128527 12459027658030849221192791)
            ·
              refine ⟨18688541487046273831789187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12459027658030849221192791 18688541487046273831789187)
              ·
                refine ⟨28032812230569410747683781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18688541487046273831789187 28032812230569410747683781)
                ·
                  refine ⟨5256152293231764515190709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28032812230569410747683781 5256152293231764515190709)
                  ·
                    refine ⟨492764277490477923299129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5256152293231764515190709 492764277490477923299129)
                    ·
                      rfl

theorem cell23_2878965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2878965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878965 prefixEnd_2878965 := by exact prefixLift 2878965
  have htrace : WordTrace (prefixWord ++ tailWord_2878965) baseStart_2878965 baseEnd_2878965 := by
    simpa [prefixWord, tailWord_2878965, baseEnd_2878965] using wordTrace_append hprefix tailTrace_2878965
  have hstable : (prefixWord ++ tailWord_2878965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878965).length < 2 ^ (prefixWord ++ tailWord_2878965).sum := by decide
  have hdescent : baseEnd_2878965 < baseStart_2878965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878968 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_2878968 : Nat := 118140960795 + 2878968 * 2 ^ 59
def prefixEnd_2878968 : Nat := 4983230072969 + 3 ^ 40 * 2878968 * 2
def baseEnd_2878968 : Nat := 1478294372913397258159873

theorem tailTrace_2878968 : CollatzResearch.WordTrace tailWord_2878968 prefixEnd_2878968 1478294372913397258159873 := by
  unfold tailWord_2878968
  simp only [CollatzResearch.WordTrace]
  refine ⟨52502294716999049717090779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70003059622665399622787705 52502294716999049717090779)
  ·
    refine ⟨78753442075498574575636169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52502294716999049717090779 78753442075498574575636169)
    ·
      refine ⟨59065081556623930931727127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78753442075498574575636169 59065081556623930931727127)
      ·
        refine ⟨88597622334935896397590691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59065081556623930931727127 88597622334935896397590691)
        ·
          refine ⟨132896433502403844596386037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88597622334935896397590691 132896433502403844596386037)
          ·
            refine ⟨12459040640850360430911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132896433502403844596386037 12459040640850360430911191)
            ·
              refine ⟨18688560961275540646366787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12459040640850360430911191 18688560961275540646366787)
              ·
                refine ⟨28032841441913310969550181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18688560961275540646366787 28032841441913310969550181)
                ·
                  refine ⟨5256157770358745806790659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28032841441913310969550181 5256157770358745806790659)
                  ·
                    refine ⟨7884236655538118710185989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5256157770358745806790659 7884236655538118710185989)
                    ·
                      refine ⟨1478294372913397258159873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7884236655538118710185989 1478294372913397258159873)
                      ·
                        rfl

theorem cell23_2878968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_2878968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878968 prefixEnd_2878968 := by exact prefixLift 2878968
  have htrace : WordTrace (prefixWord ++ tailWord_2878968) baseStart_2878968 baseEnd_2878968 := by
    simpa [prefixWord, tailWord_2878968, baseEnd_2878968] using wordTrace_append hprefix tailTrace_2878968
  have hstable : (prefixWord ++ tailWord_2878968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878968).length < 2 ^ (prefixWord ++ tailWord_2878968).sum := by decide
  have hdescent : baseEnd_2878968 < baseStart_2878968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878971 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_2878971 : Nat := 118140960795 + 2878971 * 2 ^ 59
def prefixEnd_2878971 : Nat := 4983230072969 + 3 ^ 40 * 2878971 * 2
def baseEnd_2878971 : Nat := 1478295913355360746422359

theorem tailTrace_2878971 : CollatzResearch.WordTrace tailWord_2878971 prefixEnd_2878971 1478295913355360746422359 := by
  unfold tailWord_2878971
  simp only [CollatzResearch.WordTrace]
  refine ⟨105004698852987230946540767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70003132568658153964360511 105004698852987230946540767)
  ·
    refine ⟨157507048279480846419811151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105004698852987230946540767 157507048279480846419811151)
    ·
      refine ⟨236260572419221269629716727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157507048279480846419811151 236260572419221269629716727)
      ·
        refine ⟨354390858628831904444575091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236260572419221269629716727 354390858628831904444575091)
        ·
          refine ⟨531586287943247856666862637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354390858628831904444575091 531586287943247856666862637)
          ·
            refine ⟨199344857978717946250073489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531586287943247856666862637 199344857978717946250073489)
            ·
              refine ⟨149508643484038459687555117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199344857978717946250073489 149508643484038459687555117)
              ·
                refine ⟨56065741306514422382833169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149508643484038459687555117 56065741306514422382833169)
                ·
                  refine ⟨42049305979885816787124877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56065741306514422382833169 42049305979885816787124877)
                  ·
                    refine ⟨15768489742457181295171829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42049305979885816787124877 15768489742457181295171829)
                    ·
                      refine ⟨1478295913355360746422359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15768489742457181295171829 1478295913355360746422359)
                      ·
                        rfl

theorem cell23_2878971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_2878971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2878971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2878971 prefixEnd_2878971 := by exact prefixLift 2878971
  have htrace : WordTrace (prefixWord ++ tailWord_2878971) baseStart_2878971 baseEnd_2878971 := by
    simpa [prefixWord, tailWord_2878971, baseEnd_2878971] using wordTrace_append hprefix tailTrace_2878971
  have hstable : (prefixWord ++ tailWord_2878971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878971).length < 2 ^ (prefixWord ++ tailWord_2878971).sum := by decide
  have hdescent : baseEnd_2878971 < baseStart_2878971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879001 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2879001 : Nat := 118140960795 + 2879001 * 2 ^ 59
def prefixEnd_2879001 : Nat := 4983230072969 + 3 ^ 40 * 2879001 * 2
def baseEnd_2879001 : Nat := 1478311317774995629047221

theorem tailTrace_2879001 : CollatzResearch.WordTrace tailWord_2879001 prefixEnd_2879001 1478311317774995629047221 := by
  unfold tailWord_2879001
  simp only [CollatzResearch.WordTrace]
  refine ⟨105005793042878546070132857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70003862028585697380088571 105005793042878546070132857)
  ·
    refine ⟨78754344782158909552599643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105005793042878546070132857 78754344782158909552599643)
    ·
      refine ⟨118131517173238364328899465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78754344782158909552599643 118131517173238364328899465)
      ·
        refine ⟨88598637879928773246674599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118131517173238364328899465 88598637879928773246674599)
        ·
          refine ⟨132897956819893159870011899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88598637879928773246674599 132897956819893159870011899)
          ·
            refine ⟨199346935229839739805017849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132897956819893159870011899 199346935229839739805017849)
            ·
              refine ⟨149510201422379804853763387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199346935229839739805017849 149510201422379804853763387)
              ·
                refine ⟨224265302133569707280645081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149510201422379804853763387 224265302133569707280645081)
                ·
                  refine ⟨168198976600177280460483811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224265302133569707280645081 168198976600177280460483811)
                  ·
                    refine ⟨252298464900265920690725717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168198976600177280460483811 252298464900265920690725717)
                    ·
                      refine ⟨1478311317774995629047221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 252298464900265920690725717 1478311317774995629047221)
                      ·
                        rfl

theorem cell23_2879001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2879001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879001 prefixEnd_2879001 := by exact prefixLift 2879001
  have htrace : WordTrace (prefixWord ++ tailWord_2879001) baseStart_2879001 baseEnd_2879001 := by
    simpa [prefixWord, tailWord_2879001, baseEnd_2879001] using wordTrace_append hprefix tailTrace_2879001
  have hstable : (prefixWord ++ tailWord_2879001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879001).length < 2 ^ (prefixWord ++ tailWord_2879001).sum := by decide
  have hdescent : baseEnd_2879001 < baseStart_2879001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879022 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2879022 : Nat := 118140960795 + 2879022 * 2 ^ 59
def prefixEnd_2879022 : Nat := 4983230072969 + 3 ^ 40 * 2879022 * 2
def baseEnd_2879022 : Nat := 1478322100868740046884625

theorem tailTrace_2879022 : CollatzResearch.WordTrace tailWord_2879022 prefixEnd_2879022 1478322100868740046884625 := by
  unfold tailWord_2879022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125819871975308332080915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70004372650534977771098213 13125819871975308332080915)
  ·
    refine ⟨19688729807962962498121373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13125819871975308332080915 19688729807962962498121373)
    ·
      refine ⟨7383273677986110936795515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19688729807962962498121373 7383273677986110936795515)
      ·
        refine ⟨11074910516979166405193273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383273677986110936795515 11074910516979166405193273)
        ·
          refine ⟨8306182887734374803894955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11074910516979166405193273 8306182887734374803894955)
          ·
            refine ⟨12459274331601562205842433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306182887734374803894955 12459274331601562205842433)
            ·
              refine ⟨9344455748701171654381825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12459274331601562205842433 9344455748701171654381825)
              ·
                refine ⟨7008341811525878740786369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9344455748701171654381825 7008341811525878740786369)
                ·
                  refine ⟨5256256358644409055589777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7008341811525878740786369 5256256358644409055589777)
                  ·
                    refine ⟨3942192268983306791692333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5256256358644409055589777 3942192268983306791692333)
                    ·
                      refine ⟨1478322100868740046884625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942192268983306791692333 1478322100868740046884625)
                      ·
                        rfl

theorem cell23_2879022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2879022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879022 prefixEnd_2879022 := by exact prefixLift 2879022
  have htrace : WordTrace (prefixWord ++ tailWord_2879022) baseStart_2879022 baseEnd_2879022 := by
    simpa [prefixWord, tailWord_2879022, baseEnd_2879022] using wordTrace_append hprefix tailTrace_2879022
  have hstable : (prefixWord ++ tailWord_2879022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879022).length < 2 ^ (prefixWord ++ tailWord_2879022).sum := by decide
  have hdescent : baseEnd_2879022 < baseStart_2879022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879029 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2879029 : Nat := 118140960795 + 2879029 * 2 ^ 59
def prefixEnd_2879029 : Nat := 4983230072969 + 3 ^ 40 * 2879029 * 2
def baseEnd_2879029 : Nat := 492775231744440506499031

theorem tailTrace_2879029 : CollatzResearch.WordTrace tailWord_2879029 prefixEnd_2879029 492775231744440506499031 := by
  unfold tailWord_2879029
  simp only [CollatzResearch.WordTrace]
  refine ⟨105006814286777106852152141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70004542857851404568101427 105006814286777106852152141)
  ·
    refine ⟨39377555357541415069557053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105006814286777106852152141 39377555357541415069557053)
    ·
      refine ⟨14766583259078030651083895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39377555357541415069557053 14766583259078030651083895)
      ·
        refine ⟨22149874888617045976625843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14766583259078030651083895 22149874888617045976625843)
        ·
          refine ⟨33224812332925568964938765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22149874888617045976625843 33224812332925568964938765)
          ·
            refine ⟨12459304624847088361852037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33224812332925568964938765 12459304624847088361852037)
            ·
              refine ⟨2336119617158829067847257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12459304624847088361852037 2336119617158829067847257)
              ·
                refine ⟨1752089712869121800885443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336119617158829067847257 1752089712869121800885443)
                ·
                  refine ⟨2628134569303682701328165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752089712869121800885443 2628134569303682701328165)
                  ·
                    refine ⟨492775231744440506499031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628134569303682701328165 492775231744440506499031)
                    ·
                      rfl

theorem cell23_2879029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2879029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879029 prefixEnd_2879029 := by exact prefixLift 2879029
  have htrace : WordTrace (prefixWord ++ tailWord_2879029) baseStart_2879029 baseEnd_2879029 := by
    simpa [prefixWord, tailWord_2879029, baseEnd_2879029] using wordTrace_append hprefix tailTrace_2879029
  have hstable : (prefixWord ++ tailWord_2879029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879029).length < 2 ^ (prefixWord ++ tailWord_2879029).sum := by decide
  have hdescent : baseEnd_2879029 < baseStart_2879029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879045 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_2879045 : Nat := 118140960795 + 2879045 * 2 ^ 59
def prefixEnd_2879045 : Nat := 4983230072969 + 3 ^ 40 * 2879045 * 2
def baseEnd_2879045 : Nat := 1478333910923793456897019

theorem tailTrace_2879045 : CollatzResearch.WordTrace tailWord_2879045 prefixEnd_2879045 1478333910923793456897019 := by
  unfold tailWord_2879045
  simp only [CollatzResearch.WordTrace]
  refine ⟨105007397854719141584734589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70004931903146094389823059 105007397854719141584734589)
  ·
    refine ⟨39377774195519678094275471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105007397854719141584734589 39377774195519678094275471)
    ·
      refine ⟨59066661293279517141413207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39377774195519678094275471 59066661293279517141413207)
      ·
        refine ⟨88599991939919275712119811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59066661293279517141413207 88599991939919275712119811)
        ·
          refine ⟨132899987909878913568179717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88599991939919275712119811 132899987909878913568179717)
          ·
            refine ⟨24918747733102296294033697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132899987909878913568179717 24918747733102296294033697)
            ·
              refine ⟨18689060799826722220525273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24918747733102296294033697 18689060799826722220525273)
              ·
                refine ⟨14016795599870041665393955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18689060799826722220525273 14016795599870041665393955)
                ·
                  refine ⟨21025193399805062498090933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14016795599870041665393955 21025193399805062498090933)
                  ·
                    refine ⟨1971111881231724609196025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21025193399805062498090933 1971111881231724609196025)
                    ·
                      refine ⟨1478333910923793456897019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971111881231724609196025 1478333910923793456897019)
                      ·
                        rfl

theorem cell23_2879045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_2879045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879045 prefixEnd_2879045 := by exact prefixLift 2879045
  have htrace : WordTrace (prefixWord ++ tailWord_2879045) baseStart_2879045 baseEnd_2879045 := by
    simpa [prefixWord, tailWord_2879045, baseEnd_2879045] using wordTrace_append hprefix tailTrace_2879045
  have hstable : (prefixWord ++ tailWord_2879045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879045).length < 2 ^ (prefixWord ++ tailWord_2879045).sum := by decide
  have hdescent : baseEnd_2879045 < baseStart_2879045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879052 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2879052 : Nat := 118140960795 + 2879052 * 2 ^ 59
def prefixEnd_2879052 : Nat := 4983230072969 + 3 ^ 40 * 2879052 * 2
def baseEnd_2879052 : Nat := 1478337505288374929509487

theorem tailTrace_2879052 : CollatzResearch.WordTrace tailWord_2879052 prefixEnd_2879052 1478337505288374929509487 := by
  unfold tailWord_2879052
  simp only [CollatzResearch.WordTrace]
  refine ⟨52503826582846890890119705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70005102110462521186826273 52503826582846890890119705)
  ·
    refine ⟨39377869937135168167589779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52503826582846890890119705 39377869937135168167589779)
    ·
      refine ⟨59066804905702752251384669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39377869937135168167589779 59066804905702752251384669)
      ·
        refine ⟨22150051839638532094269251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59066804905702752251384669 22150051839638532094269251)
        ·
          refine ⟨33225077759457798141403877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22150051839638532094269251 33225077759457798141403877)
          ·
            refine ⟨6229702079898337151513227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33225077759457798141403877 6229702079898337151513227)
            ·
              refine ⟨9344553119847505727269841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229702079898337151513227 9344553119847505727269841)
              ·
                refine ⟨7008414839885629295452381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9344553119847505727269841 7008414839885629295452381)
                ·
                  refine ⟨2628155564957110985794643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7008414839885629295452381 2628155564957110985794643)
                  ·
                    refine ⟨3942233347435666478691965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2628155564957110985794643 3942233347435666478691965)
                    ·
                      refine ⟨1478337505288374929509487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942233347435666478691965 1478337505288374929509487)
                      ·
                        rfl

theorem cell23_2879052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2879052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879052 prefixEnd_2879052 := by exact prefixLift 2879052
  have htrace : WordTrace (prefixWord ++ tailWord_2879052) baseStart_2879052 baseEnd_2879052 := by
    simpa [prefixWord, tailWord_2879052, baseEnd_2879052] using wordTrace_append hprefix tailTrace_2879052
  have hstable : (prefixWord ++ tailWord_2879052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879052).length < 2 ^ (prefixWord ++ tailWord_2879052).sum := by decide
  have hdescent : baseEnd_2879052 < baseStart_2879052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879105 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2879105 : Nat := 118140960795 + 2879105 * 2 ^ 59
def prefixEnd_2879105 : Nat := 4983230072969 + 3 ^ 40 * 2879105 * 2
def baseEnd_2879105 : Nat := 1478364719763063222146743

theorem tailTrace_2879105 : CollatzResearch.WordTrace tailWord_2879105 prefixEnd_2879105 1478364719763063222146743 := by
  unfold tailWord_2879105
  simp only [CollatzResearch.WordTrace]
  refine ⟨105009586234501771831918769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70006390823001181221279179 105009586234501771831918769)
  ·
    refine ⟨78757189675876328873939077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105009586234501771831918769 78757189675876328873939077)
    ·
      refine ⟨14766973064226811663863577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78757189675876328873939077 14766973064226811663863577)
      ·
        refine ⟨11075229798170108747897683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14766973064226811663863577 11075229798170108747897683)
        ·
          refine ⟨16612844697255163121846525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11075229798170108747897683 16612844697255163121846525)
          ·
            refine ⟨6229816761470686170692447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16612844697255163121846525 6229816761470686170692447)
            ·
              refine ⟨9344725142206029256038671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229816761470686170692447 9344725142206029256038671)
              ·
                refine ⟨14017087713309043884058007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344725142206029256038671 14017087713309043884058007)
                ·
                  refine ⟨21025631569963565826087011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14017087713309043884058007 21025631569963565826087011)
                  ·
                    refine ⟨31538447354945348739130517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21025631569963565826087011 31538447354945348739130517)
                    ·
                      refine ⟨1478364719763063222146743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31538447354945348739130517 1478364719763063222146743)
                      ·
                        rfl

theorem cell23_2879105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2879105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879105 prefixEnd_2879105 := by exact prefixLift 2879105
  have htrace : WordTrace (prefixWord ++ tailWord_2879105) baseStart_2879105 baseEnd_2879105 := by
    simpa [prefixWord, tailWord_2879105, baseEnd_2879105] using wordTrace_append hprefix tailTrace_2879105
  have hstable : (prefixWord ++ tailWord_2879105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879105).length < 2 ^ (prefixWord ++ tailWord_2879105).sum := by decide
  have hdescent : baseEnd_2879105 < baseStart_2879105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879125 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2879125 : Nat := 118140960795 + 2879125 * 2 ^ 59
def prefixEnd_2879125 : Nat := 4983230072969 + 3 ^ 40 * 2879125 * 2
def baseEnd_2879125 : Nat := 1478374989376153143896651

theorem tailTrace_2879125 : CollatzResearch.WordTrace tailWord_2879125 prefixEnd_2879125 1478374989376153143896651 := by
  unfold tailWord_2879125
  simp only [CollatzResearch.WordTrace]
  refine ⟨105010315694429315247646829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70006877129619543498431219 105010315694429315247646829)
  ·
    refine ⟨39378868385410993217867561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105010315694429315247646829 39378868385410993217867561)
    ·
      refine ⟨29534151289058244913400671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39378868385410993217867561 29534151289058244913400671)
      ·
        refine ⟨44301226933587367370101007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29534151289058244913400671 44301226933587367370101007)
        ·
          refine ⟨66451840400381051055151511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44301226933587367370101007 66451840400381051055151511)
          ·
            refine ⟨99677760600571576582727267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66451840400381051055151511 99677760600571576582727267)
            ·
              refine ⟨149516640900857364874090901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99677760600571576582727267 149516640900857364874090901)
              ·
                refine ⟨7008592542227688978473011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149516640900857364874090901 7008592542227688978473011)
                ·
                  refine ⟨10512888813341533467709517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7008592542227688978473011 10512888813341533467709517)
                  ·
                    refine ⟨3942333305003075050391069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10512888813341533467709517 3942333305003075050391069)
                    ·
                      refine ⟨1478374989376153143896651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942333305003075050391069 1478374989376153143896651)
                      ·
                        rfl

theorem cell23_2879125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2879125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879125 prefixEnd_2879125 := by exact prefixLift 2879125
  have htrace : WordTrace (prefixWord ++ tailWord_2879125) baseStart_2879125 baseEnd_2879125 := by
    simpa [prefixWord, tailWord_2879125, baseEnd_2879125] using wordTrace_append hprefix tailTrace_2879125
  have hstable : (prefixWord ++ tailWord_2879125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879125).length < 2 ^ (prefixWord ++ tailWord_2879125).sum := by decide
  have hdescent : baseEnd_2879125 < baseStart_2879125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879132 : List Nat := [2, 2, 3, 2, 4, 1, 9]
def baseStart_2879132 : Nat := 118140960795 + 2879132 * 2 ^ 59
def prefixEnd_2879132 : Nat := 4983230072969 + 3 ^ 40 * 2879132 * 2
def baseEnd_2879132 : Nat := 18251587453589316253199

theorem tailTrace_2879132 : CollatzResearch.WordTrace tailWord_2879132 prefixEnd_2879132 18251587453589316253199 := by
  unfold tailWord_2879132
  simp only [CollatzResearch.WordTrace]
  refine ⟨52505285502701977721575825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70007047336935970295434433 52505285502701977721575825)
  ·
    refine ⟨39378964127026483291181869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52505285502701977721575825 39378964127026483291181869)
    ·
      refine ⟨14767111547634931234193201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39378964127026483291181869 14767111547634931234193201)
      ·
        refine ⟨11075333660726198425644901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14767111547634931234193201 11075333660726198425644901)
        ·
          refine ⟨2076625061386162204808419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11075333660726198425644901 2076625061386162204808419)
          ·
            refine ⟨3114937592079243307212629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076625061386162204808419 3114937592079243307212629)
            ·
              refine ⟨18251587453589316253199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3114937592079243307212629 18251587453589316253199)
              ·
                rfl

theorem cell23_2879132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 9].length) (baseStart_2879132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879132 prefixEnd_2879132 := by exact prefixLift 2879132
  have htrace : WordTrace (prefixWord ++ tailWord_2879132) baseStart_2879132 baseEnd_2879132 := by
    simpa [prefixWord, tailWord_2879132, baseEnd_2879132] using wordTrace_append hprefix tailTrace_2879132
  have hstable : (prefixWord ++ tailWord_2879132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879132).length < 2 ^ (prefixWord ++ tailWord_2879132).sum := by decide
  have hdescent : baseEnd_2879132 < baseStart_2879132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879159 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_2879159 : Nat := 118140960795 + 2879159 * 2 ^ 59
def prefixEnd_2879159 : Nat := 4983230072969 + 3 ^ 40 * 2879159 * 2
def baseEnd_2879159 : Nat := 1478392447718406010871495

theorem tailTrace_2879159 : CollatzResearch.WordTrace tailWord_2879159 prefixEnd_2879159 1478392447718406010871495 := by
  unfold tailWord_2879159
  simp only [CollatzResearch.WordTrace]
  refine ⟨105011555776306139054384531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70007703850870759369589687 105011555776306139054384531)
  ·
    refine ⟨157517333664459208581576797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105011555776306139054384531 157517333664459208581576797)
    ·
      refine ⟨59069000124172203218091299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157517333664459208581576797 59069000124172203218091299)
      ·
        refine ⟨88603500186258304827136949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59069000124172203218091299 88603500186258304827136949)
        ·
          refine ⟨8306578142461716077544089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88603500186258304827136949 8306578142461716077544089)
          ·
            refine ⟨6229933606846287058158067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8306578142461716077544089 6229933606846287058158067)
            ·
              refine ⟨9344900410269430587237101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229933606846287058158067 9344900410269430587237101)
              ·
                refine ⟨3504337653851036470213913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9344900410269430587237101 3504337653851036470213913)
                ·
                  refine ⟨2628253240388277352660435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3504337653851036470213913 2628253240388277352660435)
                  ·
                    refine ⟨3942379860582416028990653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2628253240388277352660435 3942379860582416028990653)
                    ·
                      refine ⟨1478392447718406010871495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942379860582416028990653 1478392447718406010871495)
                      ·
                        rfl

theorem cell23_2879159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_2879159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879159 prefixEnd_2879159 := by exact prefixLift 2879159
  have htrace : WordTrace (prefixWord ++ tailWord_2879159) baseStart_2879159 baseEnd_2879159 := by
    simpa [prefixWord, tailWord_2879159, baseEnd_2879159] using wordTrace_append hprefix tailTrace_2879159
  have hstable : (prefixWord ++ tailWord_2879159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879159).length < 2 ^ (prefixWord ++ tailWord_2879159).sum := by decide
  have hdescent : baseEnd_2879159 < baseStart_2879159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879185 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2879185 : Nat := 118140960795 + 2879185 * 2 ^ 59
def prefixEnd_2879185 : Nat := 4983230072969 + 3 ^ 40 * 2879185 * 2
def baseEnd_2879185 : Nat := 1478405798215422909146375

theorem tailTrace_2879185 : CollatzResearch.WordTrace tailWord_2879185 prefixEnd_2879185 1478405798215422909146375 := by
  unfold tailWord_2879185
  simp only [CollatzResearch.WordTrace]
  refine ⟨105012504074211945494831009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70008336049474630329887339 105012504074211945494831009)
  ·
    refine ⟨78759378055658959121123257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105012504074211945494831009 78759378055658959121123257)
    ·
      refine ⟨59069533541744219340842443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78759378055658959121123257 59069533541744219340842443)
      ·
        refine ⟨88604300312616329011263665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59069533541744219340842443 88604300312616329011263665)
        ·
          refine ⟨66453225234462246758447749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88604300312616329011263665 66453225234462246758447749)
          ·
            refine ⟨12459979731461671267208953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66453225234462246758447749 12459979731461671267208953)
            ·
              refine ⟨9344984798596253450406715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12459979731461671267208953 9344984798596253450406715)
              ·
                refine ⟨14017477197894380175610073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9344984798596253450406715 14017477197894380175610073)
                ·
                  refine ⟨10513107898420785131707555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14017477197894380175610073 10513107898420785131707555)
                  ·
                    refine ⟨15769661847631177697561333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10513107898420785131707555 15769661847631177697561333)
                    ·
                      refine ⟨1478405798215422909146375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15769661847631177697561333 1478405798215422909146375)
                      ·
                        rfl

theorem cell23_2879185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2879185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879185 prefixEnd_2879185 := by exact prefixLift 2879185
  have htrace : WordTrace (prefixWord ++ tailWord_2879185) baseStart_2879185 baseEnd_2879185 := by
    simpa [prefixWord, tailWord_2879185, baseEnd_2879185] using wordTrace_append hprefix tailTrace_2879185
  have hstable : (prefixWord ++ tailWord_2879185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879185).length < 2 ^ (prefixWord ++ tailWord_2879185).sum := by decide
  have hdescent : baseEnd_2879185 < baseStart_2879185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879205 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 7]
def baseStart_2879205 : Nat := 118140960795 + 2879205 * 2 ^ 59
def prefixEnd_2879205 : Nat := 4983230072969 + 3 ^ 40 * 2879205 * 2
def baseEnd_2879205 : Nat := 164268451980945870099587

theorem tailTrace_2879205 : CollatzResearch.WordTrace tailWord_2879205 prefixEnd_2879205 164268451980945870099587 := by
  unfold tailWord_2879205
  simp only [CollatzResearch.WordTrace]
  refine ⟨105013233534139488910559069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70008822356092992607039379 105013233534139488910559069)
  ·
    refine ⟨39379962575302308341459651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105013233534139488910559069 39379962575302308341459651)
    ·
      refine ⟨59069943862953462512189477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39379962575302308341459651 59069943862953462512189477)
      ·
        refine ⟨11075614474303774221035527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59069943862953462512189477 11075614474303774221035527)
        ·
          refine ⟨16613421711455661331553291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11075614474303774221035527 16613421711455661331553291)
          ·
            refine ⟨24920132567183491997329937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16613421711455661331553291 24920132567183491997329937)
            ·
              refine ⟨18690099425387618997997453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24920132567183491997329937 18690099425387618997997453)
              ·
                refine ⟨7008787284520357124249045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18690099425387618997997453 7008787284520357124249045)
                ·
                  refine ⟨164268451980945870099587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7008787284520357124249045 164268451980945870099587)
                  ·
                    rfl

theorem cell23_2879205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_2879205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879205 prefixEnd_2879205 := by exact prefixLift 2879205
  have htrace : WordTrace (prefixWord ++ tailWord_2879205) baseStart_2879205 baseEnd_2879205 := by
    simpa [prefixWord, tailWord_2879205, baseEnd_2879205] using wordTrace_append hprefix tailTrace_2879205
  have hstable : (prefixWord ++ tailWord_2879205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879205).length < 2 ^ (prefixWord ++ tailWord_2879205).sum := by decide
  have hdescent : baseEnd_2879205 < baseStart_2879205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879222 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2879222 : Nat := 118140960795 + 2879222 * 2 ^ 59
def prefixEnd_2879222 : Nat := 4983230072969 + 3 ^ 40 * 2879222 * 2
def baseEnd_2879222 : Nat := 164269421888848807153745

theorem tailTrace_2879222 : CollatzResearch.WordTrace tailWord_2879222 prefixEnd_2879222 164269421888848807153745 := by
  unfold tailWord_2879222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563365848442368800870495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70009235716718600542618613 6563365848442368800870495)
  ·
    refine ⟨9845048772663553201305743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563365848442368800870495 9845048772663553201305743)
    ·
      refine ⟨14767573158995329801958615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845048772663553201305743 14767573158995329801958615)
      ·
        refine ⟨22151359738492994702937923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14767573158995329801958615 22151359738492994702937923)
        ·
          refine ⟨33227039607739492054406885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22151359738492994702937923 33227039607739492054406885)
          ·
            refine ⟨6230069926451154760201291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33227039607739492054406885 6230069926451154760201291)
            ·
              refine ⟨9345104889676732140301937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230069926451154760201291 9345104889676732140301937)
              ·
                refine ⟨7008828667257549105226453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345104889676732140301937 7008828667257549105226453)
                ·
                  refine ⟨164269421888848807153745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7008828667257549105226453 164269421888848807153745)
                  ·
                    rfl

theorem cell23_2879222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2879222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879222 prefixEnd_2879222 := by exact prefixLift 2879222
  have htrace : WordTrace (prefixWord ++ tailWord_2879222) baseStart_2879222 baseEnd_2879222 := by
    simpa [prefixWord, tailWord_2879222, baseEnd_2879222] using wordTrace_append hprefix tailTrace_2879222
  have hstable : (prefixWord ++ tailWord_2879222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879222).length < 2 ^ (prefixWord ++ tailWord_2879222).sum := by decide
  have hdescent : baseEnd_2879222 < baseStart_2879222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879250 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2879250 : Nat := 118140960795 + 2879250 * 2 ^ 59
def prefixEnd_2879250 : Nat := 4983230072969 + 3 ^ 40 * 2879250 * 2
def baseEnd_2879250 : Nat := 1478439174457965154833577

theorem tailTrace_2879250 : CollatzResearch.WordTrace tailWord_2879250 prefixEnd_2879250 1478439174457965154833577 := by
  unfold tailWord_2879250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26253718704744115398986801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70009916545984307730631469 26253718704744115398986801)
  ·
    refine ⟨19690289028558086549240101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26253718704744115398986801 19690289028558086549240101)
    ·
      refine ⟨3691929192854641227982519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19690289028558086549240101 3691929192854641227982519)
      ·
        refine ⟨5537893789281961841973779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691929192854641227982519 5537893789281961841973779)
        ·
          refine ⟨8306840683922942762960669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5537893789281961841973779 8306840683922942762960669)
          ·
            refine ⟨3115065256471103536110251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8306840683922942762960669 3115065256471103536110251)
            ·
              refine ⟨4672597884706655304165377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115065256471103536110251 4672597884706655304165377)
              ·
                refine ⟨3504448413529991478124033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4672597884706655304165377 3504448413529991478124033)
                ·
                  refine ⟨2628336310147493608593025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3504448413529991478124033 2628336310147493608593025)
                  ·
                    refine ⟨1971252232610620206444769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2628336310147493608593025 1971252232610620206444769)
                    ·
                      refine ⟨1478439174457965154833577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971252232610620206444769 1478439174457965154833577)
                      ·
                        rfl

theorem cell23_2879250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2879250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879250 prefixEnd_2879250 := by exact prefixLift 2879250
  have htrace : WordTrace (prefixWord ++ tailWord_2879250) baseStart_2879250 baseEnd_2879250 := by
    simpa [prefixWord, tailWord_2879250, baseEnd_2879250] using wordTrace_append hprefix tailTrace_2879250
  have hstable : (prefixWord ++ tailWord_2879250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879250).length < 2 ^ (prefixWord ++ tailWord_2879250).sum := by decide
  have hdescent : baseEnd_2879250 < baseStart_2879250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879272 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2879272 : Nat := 118140960795 + 2879272 * 2 ^ 59
def prefixEnd_2879272 : Nat := 4983230072969 + 3 ^ 40 * 2879272 * 2
def baseEnd_2879272 : Nat := 1478450471032364068758475

theorem tailTrace_2879272 : CollatzResearch.WordTrace tailWord_2879272 prefixEnd_2879272 1478450471032364068758475 := by
  unfold tailWord_2879272
  simp only [CollatzResearch.WordTrace]
  refine ⟨52507838612448379676624035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70010451483264506235498713 52507838612448379676624035)
  ·
    refine ⟨78761757918672569514936053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52507838612448379676624035 78761757918672569514936053)
    ·
      refine ⟨7383914804875553392025255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78761757918672569514936053 7383914804875553392025255)
      ·
        refine ⟨11075872207313330088037883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383914804875553392025255 11075872207313330088037883)
        ·
          refine ⟨16613808310969995132056825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11075872207313330088037883 16613808310969995132056825)
          ·
            refine ⟨12460356233227496349042619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16613808310969995132056825 12460356233227496349042619)
            ·
              refine ⟨18690534349841244523563929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12460356233227496349042619 18690534349841244523563929)
              ·
                refine ⟨14017900762380933392672947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18690534349841244523563929 14017900762380933392672947)
                ·
                  refine ⟨21026851143571400089009421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14017900762380933392672947 21026851143571400089009421)
                  ·
                    refine ⟨7885069178839275033378533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21026851143571400089009421 7885069178839275033378533)
                    ·
                      refine ⟨1478450471032364068758475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7885069178839275033378533 1478450471032364068758475)
                      ·
                        rfl

theorem cell23_2879272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2879272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879272 prefixEnd_2879272 := by exact prefixLift 2879272
  have htrace : WordTrace (prefixWord ++ tailWord_2879272) baseStart_2879272 baseEnd_2879272 := by
    simpa [prefixWord, tailWord_2879272, baseEnd_2879272] using wordTrace_append hprefix tailTrace_2879272
  have hstable : (prefixWord ++ tailWord_2879272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879272).length < 2 ^ (prefixWord ++ tailWord_2879272).sum := by decide
  have hdescent : baseEnd_2879272 < baseStart_2879272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879292 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2879292 : Nat := 118140960795 + 2879292 * 2 ^ 59
def prefixEnd_2879292 : Nat := 4983230072969 + 3 ^ 40 * 2879292 * 2
def baseEnd_2879292 : Nat := 1478460740645453990508383

theorem tailTrace_2879292 : CollatzResearch.WordTrace tailWord_2879292 prefixEnd_2879292 1478460740645453990508383 := by
  unfold tailWord_2879292
  simp only [CollatzResearch.WordTrace]
  refine ⟨52508203342412151384488065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70010937789882868512650753 52508203342412151384488065)
  ·
    refine ⟨39381152506809113538366049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52508203342412151384488065 39381152506809113538366049)
    ·
      refine ⟨29535864380106835153774537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39381152506809113538366049 29535864380106835153774537)
      ·
        refine ⟨22151898285080126365330903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29535864380106835153774537 22151898285080126365330903)
        ·
          refine ⟨33227847427620189547996355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22151898285080126365330903 33227847427620189547996355)
          ·
            refine ⟨49841771141430284321994533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33227847427620189547996355 49841771141430284321994533)
            ·
              refine ⟨9345332089018178310373975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49841771141430284321994533 9345332089018178310373975)
              ·
                refine ⟨14017998133527267465560963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9345332089018178310373975 14017998133527267465560963)
                ·
                  refine ⟨21026997200290901198341445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14017998133527267465560963 21026997200290901198341445)
                  ·
                    refine ⟨3942561975054543974689021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21026997200290901198341445 3942561975054543974689021)
                    ·
                      refine ⟨1478460740645453990508383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942561975054543974689021 1478460740645453990508383)
                      ·
                        rfl

theorem cell23_2879292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2879292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879292 prefixEnd_2879292 := by exact prefixLift 2879292
  have htrace : WordTrace (prefixWord ++ tailWord_2879292) baseStart_2879292 baseEnd_2879292 := by
    simpa [prefixWord, tailWord_2879292, baseEnd_2879292] using wordTrace_append hprefix tailTrace_2879292
  have hstable : (prefixWord ++ tailWord_2879292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879292).length < 2 ^ (prefixWord ++ tailWord_2879292).sum := by decide
  have hdescent : baseEnd_2879292 < baseStart_2879292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879316 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_2879316 : Nat := 118140960795 + 2879316 * 2 ^ 59
def prefixEnd_2879316 : Nat := 4983230072969 + 3 ^ 40 * 2879316 * 2
def baseEnd_2879316 : Nat := 492824354727053965536091

theorem tailTrace_2879316 : CollatzResearch.WordTrace tailWord_2879316 prefixEnd_2879316 492824354727053965536091 := by
  unfold tailWord_2879316
  simp only [CollatzResearch.WordTrace]
  refine ⟨52508641018368677433924901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70011521357824903245233201 52508641018368677433924901)
  ·
    refine ⟨9845370190944127018860919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52508641018368677433924901 9845370190944127018860919)
    ·
      refine ⟨14768055286416190528291379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845370190944127018860919 14768055286416190528291379)
      ·
        refine ⟨22152082929624285792437069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14768055286416190528291379 22152082929624285792437069)
        ·
          refine ⟨8307031098609107172163901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22152082929624285792437069 8307031098609107172163901)
          ·
            refine ⟨3115136661978415189561463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8307031098609107172163901 3115136661978415189561463)
            ·
              refine ⟨4672704992967622784342195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115136661978415189561463 4672704992967622784342195)
              ·
                refine ⟨7009057489451434176513293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672704992967622784342195 7009057489451434176513293)
                ·
                  refine ⟨2628396558544287816192485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7009057489451434176513293 2628396558544287816192485)
                  ·
                    refine ⟨492824354727053965536091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2628396558544287816192485 492824354727053965536091)
                    ·
                      rfl

theorem cell23_2879316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_2879316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879316 prefixEnd_2879316 := by exact prefixLift 2879316
  have htrace : WordTrace (prefixWord ++ tailWord_2879316) baseStart_2879316 baseEnd_2879316 := by
    simpa [prefixWord, tailWord_2879316, baseEnd_2879316] using wordTrace_append hprefix tailTrace_2879316
  have hstable : (prefixWord ++ tailWord_2879316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879316).length < 2 ^ (prefixWord ++ tailWord_2879316).sum := by decide
  have hdescent : baseEnd_2879316 < baseStart_2879316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879389 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2879389 : Nat := 118140960795 + 2879389 * 2 ^ 59
def prefixEnd_2879389 : Nat := 4983230072969 + 3 ^ 40 * 2879389 * 2
def baseEnd_2879389 : Nat := 492836849422980036998479

theorem tailTrace_2879389 : CollatzResearch.WordTrace tailWord_2879389 prefixEnd_2879389 492836849422980036998479 := by
  unfold tailWord_2879389
  simp only [CollatzResearch.WordTrace]
  refine ⟨105019944565472888335257221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70013296376981925556838147 105019944565472888335257221)
  ·
    refine ⟨19691239606026166562860729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105019944565472888335257221 19691239606026166562860729)
    ·
      refine ⟨14768429704519624922145547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19691239606026166562860729 14768429704519624922145547)
      ·
        refine ⟨22152644556779437383218321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14768429704519624922145547 22152644556779437383218321)
        ·
          refine ⟨16614483417584578037413741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22152644556779437383218321 16614483417584578037413741)
          ·
            refine ⟨6230431281594216764030153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16614483417584578037413741 6230431281594216764030153)
            ·
              refine ⟨4672823461195662573022615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230431281594216764030153 4672823461195662573022615)
              ·
                refine ⟨7009235191793493859533923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672823461195662573022615 7009235191793493859533923)
                ·
                  refine ⟨10513852787690240789300885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009235191793493859533923 10513852787690240789300885)
                  ·
                    refine ⟨492836849422980036998479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10513852787690240789300885 492836849422980036998479)
                    ·
                      rfl

theorem cell23_2879389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2879389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879389 prefixEnd_2879389 := by exact prefixLift 2879389
  have htrace : WordTrace (prefixWord ++ tailWord_2879389) baseStart_2879389 baseEnd_2879389 := by
    simpa [prefixWord, tailWord_2879389, baseEnd_2879389] using wordTrace_append hprefix tailTrace_2879389
  have hstable : (prefixWord ++ tailWord_2879389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879389).length < 2 ^ (prefixWord ++ tailWord_2879389).sum := by decide
  have hdescent : baseEnd_2879389 < baseStart_2879389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879390 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2879390 : Nat := 118140960795 + 2879390 * 2 ^ 59
def prefixEnd_2879390 : Nat := 4983230072969 + 3 ^ 40 * 2879390 * 2
def baseEnd_2879390 : Nat := 1478511061749594607082933

theorem tailTrace_2879390 : CollatzResearch.WordTrace tailWord_2879390 prefixEnd_2879390 1478511061749594607082933 := by
  unfold tailWord_2879390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13127497629808658188255453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70013320692312843670695749 13127497629808658188255453)
  ·
    refine ⟨4922811611178246820595795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13127497629808658188255453 4922811611178246820595795)
    ·
      refine ⟨7384217416767370230893693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4922811611178246820595795 7384217416767370230893693)
      ·
        refine ⟨2769081531287763836585135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7384217416767370230893693 2769081531287763836585135)
        ·
          refine ⟨4153622296931645754877703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769081531287763836585135 4153622296931645754877703)
          ·
            refine ⟨6230433445397468632316555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153622296931645754877703 6230433445397468632316555)
            ·
              refine ⟨9345650168096202948474833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230433445397468632316555 9345650168096202948474833)
              ·
                refine ⟨7009237626072152211356125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345650168096202948474833 7009237626072152211356125)
                ·
                  refine ⟨2628464109777057079258547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7009237626072152211356125 2628464109777057079258547)
                  ·
                    refine ⟨3942696164665585618887821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2628464109777057079258547 3942696164665585618887821)
                    ·
                      refine ⟨1478511061749594607082933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942696164665585618887821 1478511061749594607082933)
                      ·
                        rfl

theorem cell23_2879390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2879390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879390 prefixEnd_2879390 := by exact prefixLift 2879390
  have htrace : WordTrace (prefixWord ++ tailWord_2879390) baseStart_2879390 baseEnd_2879390 := by
    simpa [prefixWord, tailWord_2879390, baseEnd_2879390] using wordTrace_append hprefix tailTrace_2879390
  have hstable : (prefixWord ++ tailWord_2879390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879390).length < 2 ^ (prefixWord ++ tailWord_2879390).sum := by decide
  have hdescent : baseEnd_2879390 < baseStart_2879390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879396 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_2879396 : Nat := 118140960795 + 2879396 * 2 ^ 59
def prefixEnd_2879396 : Nat := 4983230072969 + 3 ^ 40 * 2879396 * 2
def baseEnd_2879396 : Nat := 1478514142633521583607905

theorem tailTrace_2879396 : CollatzResearch.WordTrace tailWord_2879396 prefixEnd_2879396 1478514142633521583607905 := by
  unfold tailWord_2879396
  simp only [CollatzResearch.WordTrace]
  refine ⟨52510099938223764265381021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70013466584298352353841361 52510099938223764265381021)
  ·
    refine ⟨19691287476833911599517883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52510099938223764265381021 19691287476833911599517883)
    ·
      refine ⟨29536931215250867399276825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19691287476833911599517883 29536931215250867399276825)
      ·
        refine ⟨22152698411438150549457619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29536931215250867399276825 22152698411438150549457619)
        ·
          refine ⟨33229047617157225824186429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22152698411438150549457619 33229047617157225824186429)
          ·
            refine ⟨12460892856433959684069911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33229047617157225824186429 12460892856433959684069911)
            ·
              refine ⟨18691339284650939526104867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12460892856433959684069911 18691339284650939526104867)
              ·
                refine ⟨28037008926976409289157301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18691339284650939526104867 28037008926976409289157301)
                ·
                  refine ⟨2628469586904038370858497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28037008926976409289157301 2628469586904038370858497)
                  ·
                    refine ⟨1971352190178028778143873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2628469586904038370858497 1971352190178028778143873)
                    ·
                      refine ⟨1478514142633521583607905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971352190178028778143873 1478514142633521583607905)
                      ·
                        rfl

theorem cell23_2879396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_2879396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879396 prefixEnd_2879396 := by exact prefixLift 2879396
  have htrace : WordTrace (prefixWord ++ tailWord_2879396) baseStart_2879396 baseEnd_2879396 := by
    simpa [prefixWord, tailWord_2879396, baseEnd_2879396] using wordTrace_append hprefix tailTrace_2879396
  have hstable : (prefixWord ++ tailWord_2879396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879396).length < 2 ^ (prefixWord ++ tailWord_2879396).sum := by decide
  have hdescent : baseEnd_2879396 < baseStart_2879396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879409 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2879409 : Nat := 118140960795 + 2879409 * 2 ^ 59
def prefixEnd_2879409 : Nat := 4983230072969 + 3 ^ 40 * 2879409 * 2
def baseEnd_2879409 : Nat := 1478520817882030032745345

theorem tailTrace_2879409 : CollatzResearch.WordTrace tailWord_2879409 prefixEnd_2879409 1478520817882030032745345 := by
  unfold tailWord_2879409
  simp only [CollatzResearch.WordTrace]
  refine ⟨105020674025400431750985281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70013782683600287833990187 105020674025400431750985281)
  ·
    refine ⟨78765505519050323813238961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105020674025400431750985281 78765505519050323813238961)
    ·
      refine ⟨59074129139287742859929221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78765505519050323813238961 59074129139287742859929221)
      ·
        refine ⟨11076399213616451786236729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59074129139287742859929221 11076399213616451786236729)
        ·
          refine ⟨8307299410212338839677547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11076399213616451786236729 8307299410212338839677547)
          ·
            refine ⟨12460949115318508259516321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307299410212338839677547 12460949115318508259516321)
            ·
              refine ⟨9345711836488881194637241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12460949115318508259516321 9345711836488881194637241)
              ·
                refine ⟨7009283877366660895977931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345711836488881194637241 7009283877366660895977931)
                ·
                  refine ⟨10513925816049991343966897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009283877366660895977931 10513925816049991343966897)
                  ·
                    refine ⟨7885444362037493507975173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10513925816049991343966897 7885444362037493507975173)
                    ·
                      refine ⟨1478520817882030032745345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7885444362037493507975173 1478520817882030032745345)
                      ·
                        rfl

theorem cell23_2879409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2879409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879409 prefixEnd_2879409 := by exact prefixLift 2879409
  have htrace : WordTrace (prefixWord ++ tailWord_2879409) baseStart_2879409 baseEnd_2879409 := by
    simpa [prefixWord, tailWord_2879409, baseEnd_2879409] using wordTrace_append hprefix tailTrace_2879409
  have hstable : (prefixWord ++ tailWord_2879409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879409).length < 2 ^ (prefixWord ++ tailWord_2879409).sum := by decide
  have hdescent : baseEnd_2879409 < baseStart_2879409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879413 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_2879413 : Nat := 118140960795 + 2879413 * 2 ^ 59
def prefixEnd_2879413 : Nat := 4983230072969 + 3 ^ 40 * 2879413 * 2
def baseEnd_2879413 : Nat := 1478522871804648017095327

theorem tailTrace_2879413 : CollatzResearch.WordTrace tailWord_2879413 prefixEnd_2879413 1478522871804648017095327 := by
  unfold tailWord_2879413
  simp only [CollatzResearch.WordTrace]
  refine ⟨105020819917385940434130893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70013879944923960289420595 105020819917385940434130893)
  ·
    refine ⟨39382807469019727662799085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105020819917385940434130893 39382807469019727662799085)
    ·
      refine ⟨14768552800882397873549657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39382807469019727662799085 14768552800882397873549657)
      ·
        refine ⟨11076414600661798405162243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14768552800882397873549657 11076414600661798405162243)
        ·
          refine ⟨16614621900992697607743365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11076414600661798405162243 16614621900992697607743365)
          ·
            refine ⟨3115241606436130801451881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16614621900992697607743365 3115241606436130801451881)
            ·
              refine ⟨2336431204827098101088911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115241606436130801451881 2336431204827098101088911)
              ·
                refine ⟨3504646807240647151633367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336431204827098101088911 3504646807240647151633367)
                ·
                  refine ⟨5256970210860970727450051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504646807240647151633367 5256970210860970727450051)
                  ·
                    refine ⟨7885455316291456091175077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5256970210860970727450051 7885455316291456091175077)
                    ·
                      refine ⟨1478522871804648017095327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7885455316291456091175077 1478522871804648017095327)
                      ·
                        rfl

theorem cell23_2879413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_2879413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879413 prefixEnd_2879413 := by exact prefixLift 2879413
  have htrace : WordTrace (prefixWord ++ tailWord_2879413) baseStart_2879413 baseEnd_2879413 := by
    simpa [prefixWord, tailWord_2879413, baseEnd_2879413] using wordTrace_append hprefix tailTrace_2879413
  have hstable : (prefixWord ++ tailWord_2879413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879413).length < 2 ^ (prefixWord ++ tailWord_2879413).sum := by decide
  have hdescent : baseEnd_2879413 < baseStart_2879413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879453 : List Nat := [1, 4, 3, 1, 4, 1, 2, 7]
def baseStart_2879453 : Nat := 118140960795 + 2879453 * 2 ^ 59
def prefixEnd_2879453 : Nat := 4983230072969 + 3 ^ 40 * 2879453 * 2
def baseEnd_2879453 : Nat := 54760867075215846688709

theorem tailTrace_2879453 : CollatzResearch.WordTrace tailWord_2879453 prefixEnd_2879453 54760867075215846688709 := by
  unfold tailWord_2879453
  simp only [CollatzResearch.WordTrace]
  refine ⟨105022278837241027265587013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70014852558160684843724675 105022278837241027265587013)
  ·
    refine ⟨19691677281982692612297565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105022278837241027265587013 19691677281982692612297565)
    ·
      refine ⟨7384378980743509729611587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19691677281982692612297565 7384378980743509729611587)
      ·
        refine ⟨11076568471115264594417381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7384378980743509729611587 11076568471115264594417381)
        ·
          refine ⟨2076856588334112111453259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11076568471115264594417381 2076856588334112111453259)
          ·
            refine ⟨3115284882501168167179889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2076856588334112111453259 3115284882501168167179889)
            ·
              refine ⟨2336463661875876125384917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115284882501168167179889 2336463661875876125384917)
              ·
                refine ⟨54760867075215846688709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2336463661875876125384917 54760867075215846688709)
                ·
                  rfl

theorem cell23_2879453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 7].length) (baseStart_2879453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879453 prefixEnd_2879453 := by exact prefixLift 2879453
  have htrace : WordTrace (prefixWord ++ tailWord_2879453) baseStart_2879453 baseEnd_2879453 := by
    simpa [prefixWord, tailWord_2879453, baseEnd_2879453] using wordTrace_append hprefix tailTrace_2879453
  have hstable : (prefixWord ++ tailWord_2879453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879453).length < 2 ^ (prefixWord ++ tailWord_2879453).sum := by decide
  have hdescent : baseEnd_2879453 < baseStart_2879453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879472 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_2879472 : Nat := 118140960795 + 2879472 * 2 ^ 59
def prefixEnd_2879472 : Nat := 4983230072969 + 3 ^ 40 * 2879472 * 2
def baseEnd_2879472 : Nat := 1478553167163263286257555

theorem tailTrace_2879472 : CollatzResearch.WordTrace tailWord_2879472 prefixEnd_2879472 1478553167163263286257555 := by
  unfold tailWord_2879472
  simp only [CollatzResearch.WordTrace]
  refine ⟨52511485912086096755264335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70015314549448129007019113 52511485912086096755264335)
  ·
    refine ⟨78767228868129145132896503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52511485912086096755264335 78767228868129145132896503)
    ·
      refine ⟨118150843302193717699344755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78767228868129145132896503 118150843302193717699344755)
      ·
        refine ⟨177226264953290576549017133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118150843302193717699344755 177226264953290576549017133)
        ·
          refine ⟨66459849357483966205881425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177226264953290576549017133 66459849357483966205881425)
          ·
            refine ⟨49844887018112974654411069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66459849357483966205881425 49844887018112974654411069)
            ·
              refine ⟨18691832631792365495404151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49844887018112974654411069 18691832631792365495404151)
              ·
                refine ⟨28037748947688548243106227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18691832631792365495404151 28037748947688548243106227)
                ·
                  refine ⟨42056623421532822364659341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28037748947688548243106227 42056623421532822364659341)
                  ·
                    refine ⟨15771233783074808386747253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42056623421532822364659341 15771233783074808386747253)
                    ·
                      refine ⟨1478553167163263286257555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15771233783074808386747253 1478553167163263286257555)
                      ·
                        rfl

theorem cell23_2879472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_2879472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879472 prefixEnd_2879472 := by exact prefixLift 2879472
  have htrace : WordTrace (prefixWord ++ tailWord_2879472) baseStart_2879472 baseEnd_2879472 := by
    simpa [prefixWord, tailWord_2879472, baseEnd_2879472] using wordTrace_append hprefix tailTrace_2879472
  have hstable : (prefixWord ++ tailWord_2879472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879472).length < 2 ^ (prefixWord ++ tailWord_2879472).sum := by decide
  have hdescent : baseEnd_2879472 < baseStart_2879472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879489 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_2879489 : Nat := 118140960795 + 2879489 * 2 ^ 59
def prefixEnd_2879489 : Nat := 4983230072969 + 3 ^ 40 * 2879489 * 2
def baseEnd_2879489 : Nat := 1478561896334389719744977

theorem tailTrace_2879489 : CollatzResearch.WordTrace tailWord_2879489 prefixEnd_2879489 1478561896334389719744977 := by
  unfold tailWord_2879489
  simp only [CollatzResearch.WordTrace]
  refine ⟨105023591865110605413897521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70015727910073736942598347 105023591865110605413897521)
  ·
    refine ⟨78767693898832954060423141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105023591865110605413897521 78767693898832954060423141)
    ·
      refine ⟨14768942606031178886329339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78767693898832954060423141 14768942606031178886329339)
      ·
        refine ⟨22153413909046768329494009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14768942606031178886329339 22153413909046768329494009)
        ·
          refine ⟨16615060431785076247120507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22153413909046768329494009 16615060431785076247120507)
          ·
            refine ⟨24922590647677614370680761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16615060431785076247120507 24922590647677614370680761)
            ·
              refine ⟨18691942985758210778010571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24922590647677614370680761 18691942985758210778010571)
              ·
                refine ⟨28037914478637316167015857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18691942985758210778010571 28037914478637316167015857)
                ·
                  refine ⟨21028435858977987125261893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28037914478637316167015857 21028435858977987125261893)
                  ·
                    refine ⟨3942831723558372585986605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21028435858977987125261893 3942831723558372585986605)
                    ·
                      refine ⟨1478561896334389719744977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3942831723558372585986605 1478561896334389719744977)
                      ·
                        rfl

theorem cell23_2879489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_2879489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879489 prefixEnd_2879489 := by exact prefixLift 2879489
  have htrace : WordTrace (prefixWord ++ tailWord_2879489) baseStart_2879489 baseEnd_2879489 := by
    simpa [prefixWord, tailWord_2879489, baseEnd_2879489] using wordTrace_append hprefix tailTrace_2879489
  have hstable : (prefixWord ++ tailWord_2879489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879489).length < 2 ^ (prefixWord ++ tailWord_2879489).sum := by decide
  have hdescent : baseEnd_2879489 < baseStart_2879489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879539 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 2, 5]
def baseStart_2879539 : Nat := 118140960795 + 2879539 * 2 ^ 59
def prefixEnd_2879539 : Nat := 4983230072969 + 3 ^ 40 * 2879539 * 2
def baseEnd_2879539 : Nat := 492862523455704841373249

theorem tailTrace_2879539 : CollatzResearch.WordTrace tailWord_2879539 prefixEnd_2879539 492862523455704841373249 := by
  unfold tailWord_2879539
  simp only [CollatzResearch.WordTrace]
  refine ⟨105025415514929463953217671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70016943676619642635478447 105025415514929463953217671)
  ·
    refine ⟨157538123272394195929826507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105025415514929463953217671 157538123272394195929826507)
    ·
      refine ⟨236307184908591293894739761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157538123272394195929826507 236307184908591293894739761)
      ·
        refine ⟨177230388681443470421054821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236307184908591293894739761 177230388681443470421054821)
        ·
          refine ⟨33230697877770650703947779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177230388681443470421054821 33230697877770650703947779)
          ·
            refine ⟨49846046816655976055921669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33230697877770650703947779 49846046816655976055921669)
            ·
              refine ⟨9346133778122995510485313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49846046816655976055921669 9346133778122995510485313)
              ·
                refine ⟨7009600333592246632863985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9346133778122995510485313 7009600333592246632863985)
                ·
                  refine ⟨5257200250194184974647989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009600333592246632863985 5257200250194184974647989)
                  ·
                    refine ⟨492862523455704841373249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5257200250194184974647989 492862523455704841373249)
                    ·
                      rfl

theorem cell23_2879539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 5].length) (baseStart_2879539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879539 prefixEnd_2879539 := by exact prefixLift 2879539
  have htrace : WordTrace (prefixWord ++ tailWord_2879539) baseStart_2879539 baseEnd_2879539 := by
    simpa [prefixWord, tailWord_2879539, baseEnd_2879539] using wordTrace_append hprefix tailTrace_2879539
  have hstable : (prefixWord ++ tailWord_2879539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879539).length < 2 ^ (prefixWord ++ tailWord_2879539).sum := by decide
  have hdescent : baseEnd_2879539 < baseStart_2879539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879549 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2879549 : Nat := 118140960795 + 2879549 * 2 ^ 59
def prefixEnd_2879549 : Nat := 4983230072969 + 3 ^ 40 * 2879549 * 2
def baseEnd_2879549 : Nat := 1478592705173659484994701

theorem tailTrace_2879549 : CollatzResearch.WordTrace tailWord_2879549 prefixEnd_2879549 1478592705173659484994701 := by
  unfold tailWord_2879549
  simp only [CollatzResearch.WordTrace]
  refine ⟨105025780244893235661081701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70017186829928823774054467 105025780244893235661081701)
  ·
    refine ⟨19692333795917481686452819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105025780244893235661081701 19692333795917481686452819)
    ·
      refine ⟨29538500693876222529679229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19692333795917481686452819 29538500693876222529679229)
      ·
        refine ⟨11076937760203583448629711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29538500693876222529679229 11076937760203583448629711)
        ·
          refine ⟨16615406640305375172944567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11076937760203583448629711 16615406640305375172944567)
          ·
            refine ⟨24923109960458062759416851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16615406640305375172944567 24923109960458062759416851)
            ·
              refine ⟨37384664940687094139125277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24923109960458062759416851 37384664940687094139125277)
              ·
                refine ⟨14019249352757660302171979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37384664940687094139125277 14019249352757660302171979)
                ·
                  refine ⟨21028874029136490453257969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14019249352757660302171979 21028874029136490453257969)
                  ·
                    refine ⟨15771655521852367839943477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21028874029136490453257969 15771655521852367839943477)
                    ·
                      refine ⟨1478592705173659484994701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15771655521852367839943477 1478592705173659484994701)
                      ·
                        rfl

theorem cell23_2879549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2879549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879549 prefixEnd_2879549 := by exact prefixLift 2879549
  have htrace : WordTrace (prefixWord ++ tailWord_2879549) baseStart_2879549 baseEnd_2879549 := by
    simpa [prefixWord, tailWord_2879549, baseEnd_2879549] using wordTrace_append hprefix tailTrace_2879549
  have hstable : (prefixWord ++ tailWord_2879549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879549).length < 2 ^ (prefixWord ++ tailWord_2879549).sum := by decide
  have hdescent : baseEnd_2879549 < baseStart_2879549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879559 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2879559 : Nat := 118140960795 + 2879559 * 2 ^ 59
def prefixEnd_2879559 : Nat := 4983230072969 + 3 ^ 40 * 2879559 * 2
def baseEnd_2879559 : Nat := 1478597839980204445869655

theorem tailTrace_2879559 : CollatzResearch.WordTrace tailWord_2879559 prefixEnd_2879559 1478597839980204445869655 := by
  unfold tailWord_2879559
  simp only [CollatzResearch.WordTrace]
  refine ⟨105026144974857007368945731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70017429983238004912630487 105026144974857007368945731)
  ·
    refine ⟨157539217462285511053418597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105026144974857007368945731 157539217462285511053418597)
    ·
      refine ⟨29538603274178533322515987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157539217462285511053418597 29538603274178533322515987)
      ·
        refine ⟨44307904911267799983773981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29538603274178533322515987 44307904911267799983773981)
        ·
          refine ⟨16615464341725424993915243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44307904911267799983773981 16615464341725424993915243)
          ·
            refine ⟨24923196512588137490872865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16615464341725424993915243 24923196512588137490872865)
            ·
              refine ⟨18692397384441103118154649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24923196512588137490872865 18692397384441103118154649)
              ·
                refine ⟨14019298038330827338615987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18692397384441103118154649 14019298038330827338615987)
                ·
                  refine ⟨21028947057496241007923981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14019298038330827338615987 21028947057496241007923981)
                  ·
                    refine ⟨7885855146561090377971493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21028947057496241007923981 7885855146561090377971493)
                    ·
                      refine ⟨1478597839980204445869655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7885855146561090377971493 1478597839980204445869655)
                      ·
                        rfl

theorem cell23_2879559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2879559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879559 prefixEnd_2879559 := by exact prefixLift 2879559
  have htrace : WordTrace (prefixWord ++ tailWord_2879559) baseStart_2879559 baseEnd_2879559 := by
    simpa [prefixWord, tailWord_2879559, baseEnd_2879559] using wordTrace_append hprefix tailTrace_2879559
  have hstable : (prefixWord ++ tailWord_2879559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879559).length < 2 ^ (prefixWord ++ tailWord_2879559).sum := by decide
  have hdescent : baseEnd_2879559 < baseStart_2879559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879576 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_2879576 : Nat := 118140960795 + 2879576 * 2 ^ 59
def prefixEnd_2879576 : Nat := 4983230072969 + 3 ^ 40 * 2879576 * 2
def baseEnd_2879576 : Nat := 1478606569151330879357077

theorem tailTrace_2879576 : CollatzResearch.WordTrace tailWord_2879576 prefixEnd_2879576 1478606569151330879357077 := by
  unfold tailWord_2879576
  simp only [CollatzResearch.WordTrace]
  refine ⟨52513382507897709636157291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70017843343863612848209721 52513382507897709636157291)
  ·
    refine ⟨78770073761846564454235937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52513382507897709636157291 78770073761846564454235937)
    ·
      refine ⟨59077555321384923340676953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78770073761846564454235937 59077555321384923340676953)
      ·
        refine ⟨44308166491038692505507715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59077555321384923340676953 44308166491038692505507715)
        ·
          refine ⟨66462249736558038758261573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44308166491038692505507715 66462249736558038758261573)
          ·
            refine ⟨12461671825604632267174045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66462249736558038758261573 12461671825604632267174045)
            ·
              refine ⟨4673126934601737100190267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12461671825604632267174045 4673126934601737100190267)
              ·
                refine ⟨7009690401902605650285401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673126934601737100190267 7009690401902605650285401)
                ·
                  refine ⟨5257267801426954237714051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009690401902605650285401 5257267801426954237714051)
                  ·
                    refine ⟨7885901702140431356571077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257267801426954237714051 7885901702140431356571077)
                    ·
                      refine ⟨1478606569151330879357077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7885901702140431356571077 1478606569151330879357077)
                      ·
                        rfl

theorem cell23_2879576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_2879576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879576 prefixEnd_2879576 := by exact prefixLift 2879576
  have htrace : WordTrace (prefixWord ++ tailWord_2879576) baseStart_2879576 baseEnd_2879576 := by
    simpa [prefixWord, tailWord_2879576, baseEnd_2879576] using wordTrace_append hprefix tailTrace_2879576
  have hstable : (prefixWord ++ tailWord_2879576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879576).length < 2 ^ (prefixWord ++ tailWord_2879576).sum := by decide
  have hdescent : baseEnd_2879576 < baseStart_2879576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879589 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2879589 : Nat := 118140960795 + 2879589 * 2 ^ 59
def prefixEnd_2879589 : Nat := 4983230072969 + 3 ^ 40 * 2879589 * 2
def baseEnd_2879589 : Nat := 1478613244399839328494517

theorem tailTrace_2879589 : CollatzResearch.WordTrace tailWord_2879589 prefixEnd_2879589 1478613244399839328494517 := by
  unfold tailWord_2879589
  simp only [CollatzResearch.WordTrace]
  refine ⟨105027239164748322492537821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70018159443165548328358547 105027239164748322492537821)
  ·
    refine ⟨39385214686780620934701683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105027239164748322492537821 39385214686780620934701683)
    ·
      refine ⟨59077822030170931402052525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39385214686780620934701683 59077822030170931402052525)
      ·
        refine ⟨22154183261314099275769697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59077822030170931402052525 22154183261314099275769697)
        ·
          refine ⟨16615637445985574456827273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22154183261314099275769697 16615637445985574456827273)
          ·
            refine ⟨12461728084489180842620455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16615637445985574456827273 12461728084489180842620455)
            ·
              refine ⟨18692592126733771263930683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12461728084489180842620455 18692592126733771263930683)
              ·
                refine ⟨28038888190100656895896025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18692592126733771263930683 28038888190100656895896025)
                ·
                  refine ⟨21029166142575492671922019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28038888190100656895896025 21029166142575492671922019)
                  ·
                    refine ⟨31543749213863239007883029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21029166142575492671922019 31543749213863239007883029)
                    ·
                      refine ⟨1478613244399839328494517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31543749213863239007883029 1478613244399839328494517)
                      ·
                        rfl

theorem cell23_2879589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2879589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879589 prefixEnd_2879589 := by exact prefixLift 2879589
  have htrace : WordTrace (prefixWord ++ tailWord_2879589) baseStart_2879589 baseEnd_2879589 := by
    simpa [prefixWord, tailWord_2879589, baseEnd_2879589] using wordTrace_append hprefix tailTrace_2879589
  have hstable : (prefixWord ++ tailWord_2879589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879589).length < 2 ^ (prefixWord ++ tailWord_2879589).sum := by decide
  have hdescent : baseEnd_2879589 < baseStart_2879589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879599 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 8]
def baseStart_2879599 : Nat := 118140960795 + 2879599 * 2 ^ 59
def prefixEnd_2879599 : Nat := 4983230072969 + 3 ^ 40 * 2879599 * 2
def baseEnd_2879599 : Nat := 164290931022931587707719

theorem tailTrace_2879599 : CollatzResearch.WordTrace tailWord_2879599 prefixEnd_2879599 164290931022931587707719 := by
  unfold tailWord_2879599
  simp only [CollatzResearch.WordTrace]
  refine ⟨105027603894712094200401851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70018402596474729466934567 105027603894712094200401851)
  ·
    refine ⟨157541405842068141300602777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105027603894712094200401851 157541405842068141300602777)
    ·
      refine ⟨118156054381551105975452083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157541405842068141300602777 118156054381551105975452083)
      ·
        refine ⟨177234081572326658963178125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118156054381551105975452083 177234081572326658963178125)
        ·
          refine ⟨66462780589622497111191797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177234081572326658963178125 66462780589622497111191797)
          ·
            refine ⟨6230885680277109104174231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66462780589622497111191797 6230885680277109104174231)
            ·
              refine ⟨9346328520415663656261347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230885680277109104174231 9346328520415663656261347)
              ·
                refine ⟨14019492780623495484392021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9346328520415663656261347 14019492780623495484392021)
                ·
                  refine ⟨164290931022931587707719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14019492780623495484392021 164290931022931587707719)
                  ·
                    rfl

theorem cell23_2879599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 8].length) (baseStart_2879599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879599 prefixEnd_2879599 := by exact prefixLift 2879599
  have htrace : WordTrace (prefixWord ++ tailWord_2879599) baseStart_2879599 baseEnd_2879599 := by
    simpa [prefixWord, tailWord_2879599, baseEnd_2879599] using wordTrace_append hprefix tailTrace_2879599
  have hstable : (prefixWord ++ tailWord_2879599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879599).length < 2 ^ (prefixWord ++ tailWord_2879599).sum := by decide
  have hdescent : baseEnd_2879599 < baseStart_2879599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879653 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_2879653 : Nat := 118140960795 + 2879653 * 2 ^ 59
def prefixEnd_2879653 : Nat := 4983230072969 + 3 ^ 40 * 2879653 * 2
def baseEnd_2879653 : Nat := 1478646107161727078094223

theorem tailTrace_2879653 : CollatzResearch.WordTrace tailWord_2879653 prefixEnd_2879653 1478646107161727078094223 := by
  unfold tailWord_2879653
  simp only [CollatzResearch.WordTrace]
  refine ⟨105029573436516461422867613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70019715624344307615245075 105029573436516461422867613)
  ·
    refine ⟨39386090038693673033575355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105029573436516461422867613 39386090038693673033575355)
    ·
      refine ⟨59079135058040509550363033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39386090038693673033575355 59079135058040509550363033)
      ·
        refine ⟨44309351293530382162772275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59079135058040509550363033 44309351293530382162772275)
        ·
          refine ⟨66464026940295573244158413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44309351293530382162772275 66464026940295573244158413)
          ·
            refine ⟨24924010102610839966559405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66464026940295573244158413 24924010102610839966559405)
            ·
              refine ⟨9346503788479064987459777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24924010102610839966559405 9346503788479064987459777)
              ·
                refine ⟨7009877841359298740594833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9346503788479064987459777 7009877841359298740594833)
                ·
                  refine ⟨5257408381019474055446125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009877841359298740594833 5257408381019474055446125)
                  ·
                    refine ⟨1971528142882302770792297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5257408381019474055446125 1971528142882302770792297)
                    ·
                      refine ⟨1478646107161727078094223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971528142882302770792297 1478646107161727078094223)
                      ·
                        rfl

theorem cell23_2879653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_2879653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879653 prefixEnd_2879653 := by exact prefixLift 2879653
  have htrace : WordTrace (prefixWord ++ tailWord_2879653) baseStart_2879653 baseEnd_2879653 := by
    simpa [prefixWord, tailWord_2879653, baseEnd_2879653] using wordTrace_append hprefix tailTrace_2879653
  have hstable : (prefixWord ++ tailWord_2879653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879653).length < 2 ^ (prefixWord ++ tailWord_2879653).sum := by decide
  have hdescent : baseEnd_2879653 < baseStart_2879653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879666 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_2879666 : Nat := 118140960795 + 2879666 * 2 ^ 59
def prefixEnd_2879666 : Nat := 4983230072969 + 3 ^ 40 * 2879666 * 2
def baseEnd_2879666 : Nat := 1478652782410235527231663

theorem tailTrace_2879666 : CollatzResearch.WordTrace tailWord_2879666 prefixEnd_2879666 1478652782410235527231663 := by
  unfold tailWord_2879666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26257511896367341160772713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70020031723646243095393901 26257511896367341160772713)
  ·
    refine ⟨19693133922275505870579535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26257511896367341160772713 19693133922275505870579535)
    ·
      refine ⟨29539700883413258805869303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19693133922275505870579535 29539700883413258805869303)
      ·
        refine ⟨44309551325119888208803955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29539700883413258805869303 44309551325119888208803955)
        ·
          refine ⟨66464326987679832313205933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44309551325119888208803955 66464326987679832313205933)
          ·
            refine ⟨24924122620379937117452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66464326987679832313205933 24924122620379937117452225)
            ·
              refine ⟨18693091965284952838089169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24924122620379937117452225 18693091965284952838089169)
              ·
                refine ⟨14019818973963714628566877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18693091965284952838089169 14019818973963714628566877)
                ·
                  refine ⟨5257432115236392985712579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14019818973963714628566877 5257432115236392985712579)
                  ·
                    refine ⟨7886148172854589478568869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257432115236392985712579 7886148172854589478568869)
                    ·
                      refine ⟨1478652782410235527231663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7886148172854589478568869 1478652782410235527231663)
                      ·
                        rfl

theorem cell23_2879666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_2879666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879666 prefixEnd_2879666 := by exact prefixLift 2879666
  have htrace : WordTrace (prefixWord ++ tailWord_2879666) baseStart_2879666 baseEnd_2879666 := by
    simpa [prefixWord, tailWord_2879666, baseEnd_2879666] using wordTrace_append hprefix tailTrace_2879666
  have hstable : (prefixWord ++ tailWord_2879666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879666).length < 2 ^ (prefixWord ++ tailWord_2879666).sum := by decide
  have hdescent : baseEnd_2879666 < baseStart_2879666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879716 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_2879716 : Nat := 118140960795 + 2879716 * 2 ^ 59
def prefixEnd_2879716 : Nat := 4983230072969 + 3 ^ 40 * 2879716 * 2
def baseEnd_2879716 : Nat := 1478678456442960331606433

theorem tailTrace_2879716 : CollatzResearch.WordTrace tailWord_2879716 prefixEnd_2879716 1478678456442960331606433 := by
  unfold tailWord_2879716
  simp only [CollatzResearch.WordTrace]
  refine ⟨52515935617644111591205501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70021247490192148788274001 52515935617644111591205501)
  ·
    refine ⟨19693475856616541846702063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52515935617644111591205501 19693475856616541846702063)
    ·
      refine ⟨29540213784924812770053095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19693475856616541846702063 29540213784924812770053095)
      ·
        refine ⟨44310320677387219155079643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29540213784924812770053095 44310320677387219155079643)
        ·
          refine ⟨66465481016080828732619465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44310320677387219155079643 66465481016080828732619465)
          ·
            refine ⟨49849110762060621549464599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66465481016080828732619465 49849110762060621549464599)
            ·
              refine ⟨74773666143090932324196899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49849110762060621549464599 74773666143090932324196899)
              ·
                refine ⟨112160499214636398486295349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74773666143090932324196899 112160499214636398486295349)
                ·
                  refine ⟨10515046801372162358090189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112160499214636398486295349 10515046801372162358090189)
                  ·
                    refine ⟨3943142550514560884283821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10515046801372162358090189 3943142550514560884283821)
                    ·
                      refine ⟨1478678456442960331606433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943142550514560884283821 1478678456442960331606433)
                      ·
                        rfl

theorem cell23_2879716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_2879716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879716 prefixEnd_2879716 := by exact prefixLift 2879716
  have htrace : WordTrace (prefixWord ++ tailWord_2879716) baseStart_2879716 baseEnd_2879716 := by
    simpa [prefixWord, tailWord_2879716, baseEnd_2879716] using wordTrace_append hprefix tailTrace_2879716
  have hstable : (prefixWord ++ tailWord_2879716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879716).length < 2 ^ (prefixWord ++ tailWord_2879716).sum := by decide
  have hdescent : baseEnd_2879716 < baseStart_2879716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879743 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 3, 3, 2]
def baseStart_2879743 : Nat := 118140960795 + 2879743 * 2 ^ 59
def prefixEnd_2879743 : Nat := 4983230072969 + 3 ^ 40 * 2879743 * 2
def baseEnd_2879743 : Nat := 1478692320420631725968809

theorem tailTrace_2879743 : CollatzResearch.WordTrace tailWord_2879743 prefixEnd_2879743 1478692320420631725968809 := by
  unfold tailWord_2879743
  simp only [CollatzResearch.WordTrace]
  refine ⟨105032856006190406793643883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70021904004126937862429255 105032856006190406793643883)
  ·
    refine ⟨157549284009285610190465825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105032856006190406793643883 157549284009285610190465825)
    ·
      refine ⟨118161963006964207642849369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157549284009285610190465825 118161963006964207642849369)
      ·
        refine ⟨88621472255223155732137027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118161963006964207642849369 88621472255223155732137027)
        ·
          refine ⟨132932208382834733598205541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88621472255223155732137027 132932208382834733598205541)
          ·
            refine ⟨24924789071781512549663539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132932208382834733598205541 24924789071781512549663539)
            ·
              refine ⟨37387183607672268824495309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24924789071781512549663539 37387183607672268824495309)
              ·
                refine ⟨14020193852877100809185741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37387183607672268824495309 14020193852877100809185741)
                ·
                  refine ⟨5257572694828912803444653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14020193852877100809185741 5257572694828912803444653)
                  ·
                    refine ⟨1971589760560842301291745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5257572694828912803444653 1971589760560842301291745)
                    ·
                      refine ⟨1478692320420631725968809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971589760560842301291745 1478692320420631725968809)
                      ·
                        rfl

theorem cell23_2879743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_2879743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879743 prefixEnd_2879743 := by exact prefixLift 2879743
  have htrace : WordTrace (prefixWord ++ tailWord_2879743) baseStart_2879743 baseEnd_2879743 := by
    simpa [prefixWord, tailWord_2879743, baseEnd_2879743] using wordTrace_append hprefix tailTrace_2879743
  have hstable : (prefixWord ++ tailWord_2879743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879743).length < 2 ^ (prefixWord ++ tailWord_2879743).sum := by decide
  have hdescent : baseEnd_2879743 < baseStart_2879743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879751 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2879751 : Nat := 118140960795 + 2879751 * 2 ^ 59
def prefixEnd_2879751 : Nat := 4983230072969 + 3 ^ 40 * 2879751 * 2
def baseEnd_2879751 : Nat := 1478696428265867694668773

theorem tailTrace_2879751 : CollatzResearch.WordTrace tailWord_2879751 prefixEnd_2879751 1478696428265867694668773 := by
  unfold tailWord_2879751
  simp only [CollatzResearch.WordTrace]
  refine ⟨105033147790161424159935107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70022098526774282773290071 105033147790161424159935107)
  ·
    refine ⟨157549721685242136239902661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105033147790161424159935107 157549721685242136239902661)
    ·
      refine ⟨29540572815982900544981749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157549721685242136239902661 29540572815982900544981749)
      ·
        refine ⟨2769428701498396926092039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29540572815982900544981749 2769428701498396926092039)
        ·
          refine ⟨4154143052247595389138059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769428701498396926092039 4154143052247595389138059)
          ·
            refine ⟨6231214578371393083707089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154143052247595389138059 6231214578371393083707089)
            ·
              refine ⟨4673410933778544812780317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231214578371393083707089 4673410933778544812780317)
              ·
                refine ⟨1752529100166954304792619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4673410933778544812780317 1752529100166954304792619)
                ·
                  refine ⟨2628793650250431457188929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752529100166954304792619 2628793650250431457188929)
                  ·
                    refine ⟨1971595237687823592891697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2628793650250431457188929 1971595237687823592891697)
                    ·
                      refine ⟨1478696428265867694668773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971595237687823592891697 1478696428265867694668773)
                      ·
                        rfl

theorem cell23_2879751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2879751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879751 prefixEnd_2879751 := by exact prefixLift 2879751
  have htrace : WordTrace (prefixWord ++ tailWord_2879751) baseStart_2879751 baseEnd_2879751 := by
    simpa [prefixWord, tailWord_2879751, baseEnd_2879751] using wordTrace_append hprefix tailTrace_2879751
  have hstable : (prefixWord ++ tailWord_2879751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879751).length < 2 ^ (prefixWord ++ tailWord_2879751).sum := by decide
  have hdescent : baseEnd_2879751 < baseStart_2879751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879767 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2879767 : Nat := 118140960795 + 2879767 * 2 ^ 59
def prefixEnd_2879767 : Nat := 4983230072969 + 3 ^ 40 * 2879767 * 2
def baseEnd_2879767 : Nat := 1478704643956339632068699

theorem tailTrace_2879767 : CollatzResearch.WordTrace tailWord_2879767 prefixEnd_2879767 1478704643956339632068699 := by
  unfold tailWord_2879767
  simp only [CollatzResearch.WordTrace]
  refine ⟨105033731358103458892517555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70022487572068972595011703 105033731358103458892517555)
  ·
    refine ⟨157550597037155188338776333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105033731358103458892517555 157550597037155188338776333)
    ·
      refine ⟨59081473888933195627041125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157550597037155188338776333 59081473888933195627041125)
      ·
        refine ⟨11077776354174974180070211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59081473888933195627041125 11077776354174974180070211)
        ·
          refine ⟨16616664531262461270105317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11077776354174974180070211 16616664531262461270105317)
          ·
            refine ⟨3115624599611711488144747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16616664531262461270105317 3115624599611711488144747)
            ·
              refine ⟨4673436899417567232217121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115624599611711488144747 4673436899417567232217121)
              ·
                refine ⟨3505077674563175424162841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673436899417567232217121 3505077674563175424162841)
                ·
                  refine ⟨2628808255922381568122131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505077674563175424162841 2628808255922381568122131)
                  ·
                    refine ⟨3943212383883572352183197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2628808255922381568122131 3943212383883572352183197)
                    ·
                      refine ⟨1478704643956339632068699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943212383883572352183197 1478704643956339632068699)
                      ·
                        rfl

theorem cell23_2879767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2879767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879767 prefixEnd_2879767 := by exact prefixLift 2879767
  have htrace : WordTrace (prefixWord ++ tailWord_2879767) baseStart_2879767 baseEnd_2879767 := by
    simpa [prefixWord, tailWord_2879767, baseEnd_2879767] using wordTrace_append hprefix tailTrace_2879767
  have hstable : (prefixWord ++ tailWord_2879767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879767).length < 2 ^ (prefixWord ++ tailWord_2879767).sum := by decide
  have hdescent : baseEnd_2879767 < baseStart_2879767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879784 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2879784 : Nat := 118140960795 + 2879784 * 2 ^ 59
def prefixEnd_2879784 : Nat := 4983230072969 + 3 ^ 40 * 2879784 * 2
def baseEnd_2879784 : Nat := 1478713373127466065556121

theorem tailTrace_2879784 : CollatzResearch.WordTrace tailWord_2879784 prefixEnd_2879784 1478713373127466065556121 := by
  unfold tailWord_2879784
  simp only [CollatzResearch.WordTrace]
  refine ⟨52517175699520935397943203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70022900932694580530590937 52517175699520935397943203)
  ·
    refine ⟨78775763549281403096914805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52517175699520935397943203 78775763549281403096914805)
    ·
      refine ⟨7385227832745131540335763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78775763549281403096914805 7385227832745131540335763)
      ·
        refine ⟨11077841749117697310503645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385227832745131540335763 11077841749117697310503645)
        ·
          refine ⟨4154190655919136491438867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11077841749117697310503645 4154190655919136491438867)
          ·
            refine ⟨6231285983878704737158301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154190655919136491438867 6231285983878704737158301)
            ·
              refine ⟨2336732243954514276434363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6231285983878704737158301 2336732243954514276434363)
              ·
                refine ⟨3505098365931771414651545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336732243954514276434363 3505098365931771414651545)
                ·
                  refine ⟨2628823774448828560988659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505098365931771414651545 2628823774448828560988659)
                  ·
                    refine ⟨3943235661673242841482989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2628823774448828560988659 3943235661673242841482989)
                    ·
                      refine ⟨1478713373127466065556121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943235661673242841482989 1478713373127466065556121)
                      ·
                        rfl

theorem cell23_2879784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2879784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879784 prefixEnd_2879784 := by exact prefixLift 2879784
  have htrace : WordTrace (prefixWord ++ tailWord_2879784) baseStart_2879784 baseEnd_2879784 := by
    simpa [prefixWord, tailWord_2879784, baseEnd_2879784] using wordTrace_append hprefix tailTrace_2879784
  have hstable : (prefixWord ++ tailWord_2879784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879784).length < 2 ^ (prefixWord ++ tailWord_2879784).sum := by decide
  have hdescent : baseEnd_2879784 < baseStart_2879784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879833 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 2, 5, 2]
def baseStart_2879833 : Nat := 118140960795 + 2879833 * 2 ^ 59
def prefixEnd_2879833 : Nat := 4983230072969 + 3 ^ 40 * 2879833 * 2
def baseEnd_2879833 : Nat := 1478738533679536373843395

theorem tailTrace_2879833 : CollatzResearch.WordTrace tailWord_2879833 prefixEnd_2879833 1478738533679536373843395 := by
  unfold tailWord_2879833
  simp only [CollatzResearch.WordTrace]
  refine ⟨105036138575864352164420153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70024092383909568109613435 105036138575864352164420153)
  ·
    refine ⟨78777103931898264123315115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105036138575864352164420153 78777103931898264123315115)
    ·
      refine ⟨118165655897847396184972673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78777103931898264123315115 118165655897847396184972673)
      ·
        refine ⟨88624241923385547138729505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118165655897847396184972673 88624241923385547138729505)
        ·
          refine ⟨66468181442539160354047129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88624241923385547138729505 66468181442539160354047129)
          ·
            refine ⟨49851136081904370265535347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66468181442539160354047129 49851136081904370265535347)
            ·
              refine ⟨74776704122856555398303021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49851136081904370265535347 74776704122856555398303021)
              ·
                refine ⟨28041264046071208274363633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74776704122856555398303021 28041264046071208274363633)
                ·
                  refine ⟨21030948034553406205772725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28041264046071208274363633 21030948034553406205772725)
                  ·
                    refine ⟨1971651378239381831791193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21030948034553406205772725 1971651378239381831791193)
                    ·
                      refine ⟨1478738533679536373843395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971651378239381831791193 1478738533679536373843395)
                      ·
                        rfl

theorem cell23_2879833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_2879833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879833 prefixEnd_2879833 := by exact prefixLift 2879833
  have htrace : WordTrace (prefixWord ++ tailWord_2879833) baseStart_2879833 baseEnd_2879833 := by
    simpa [prefixWord, tailWord_2879833, baseEnd_2879833] using wordTrace_append hprefix tailTrace_2879833
  have hstable : (prefixWord ++ tailWord_2879833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879833).length < 2 ^ (prefixWord ++ tailWord_2879833).sum := by decide
  have hdescent : baseEnd_2879833 < baseStart_2879833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879863 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_2879863 : Nat := 118140960795 + 2879863 * 2 ^ 59
def prefixEnd_2879863 : Nat := 4983230072969 + 3 ^ 40 * 2879863 * 2
def baseEnd_2879863 : Nat := 1478753938099171256468257

theorem tailTrace_2879863 : CollatzResearch.WordTrace tailWord_2879863 prefixEnd_2879863 1478753938099171256468257 := by
  unfold tailWord_2879863
  simp only [CollatzResearch.WordTrace]
  refine ⟨105037232765755667288012243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70024821843837111525341495 105037232765755667288012243)
  ·
    refine ⟨157555849148633500932018365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105037232765755667288012243 157555849148633500932018365)
    ·
      refine ⟨59083443430737562849506887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157555849148633500932018365 59083443430737562849506887)
      ·
        refine ⟨88625165146106344274260331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59083443430737562849506887 88625165146106344274260331)
        ·
          refine ⟨132937747719159516411390497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88625165146106344274260331 132937747719159516411390497)
          ·
            refine ⟨99703310789369637308542873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132937747719159516411390497 99703310789369637308542873)
            ·
              refine ⟨74777483092027227981407155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99703310789369637308542873 74777483092027227981407155)
              ·
                refine ⟨112166224638040841972110733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74777483092027227981407155 112166224638040841972110733)
                ·
                  refine ⟨42062334239265315739541525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112166224638040841972110733 42062334239265315739541525)
                  ·
                    refine ⟨1971671917465561675291009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42062334239265315739541525 1971671917465561675291009)
                    ·
                      refine ⟨1478753938099171256468257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971671917465561675291009 1478753938099171256468257)
                      ·
                        rfl

theorem cell23_2879863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_2879863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879863 prefixEnd_2879863 := by exact prefixLift 2879863
  have htrace : WordTrace (prefixWord ++ tailWord_2879863) baseStart_2879863 baseEnd_2879863 := by
    simpa [prefixWord, tailWord_2879863, baseEnd_2879863] using wordTrace_append hprefix tailTrace_2879863
  have hstable : (prefixWord ++ tailWord_2879863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879863).length < 2 ^ (prefixWord ++ tailWord_2879863).sum := by decide
  have hdescent : baseEnd_2879863 < baseStart_2879863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879866 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_2879866 : Nat := 118140960795 + 2879866 * 2 ^ 59
def prefixEnd_2879866 : Nat := 4983230072969 + 3 ^ 40 * 2879866 * 2
def baseEnd_2879866 : Nat := 1478755478541134744730743

theorem tailTrace_2879866 : CollatzResearch.WordTrace tailWord_2879866 prefixEnd_2879866 1478755478541134744730743 := by
  unfold tailWord_2879866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259335546186199700092863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70024894789829865866914301 26259335546186199700092863)
  ·
    refine ⟨39389003319279299550139295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26259335546186199700092863 39389003319279299550139295)
    ·
      refine ⟨59083504978918949325208943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39389003319279299550139295 59083504978918949325208943)
      ·
        refine ⟨88625257468378423987813415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59083504978918949325208943 88625257468378423987813415)
        ·
          refine ⟨132937886202567635981720123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88625257468378423987813415 132937886202567635981720123)
          ·
            refine ⟨199406829303851453972580185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132937886202567635981720123 199406829303851453972580185)
            ·
              refine ⟨149555121977888590479435139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199406829303851453972580185 149555121977888590479435139)
              ·
                refine ⟨224332682966832885719152709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149555121977888590479435139 224332682966832885719152709)
                ·
                  refine ⟨42062378056281166072341133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224332682966832885719152709 42062378056281166072341133)
                  ·
                    refine ⟨15773391771105437277127925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42062378056281166072341133 15773391771105437277127925)
                    ·
                      refine ⟨1478755478541134744730743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15773391771105437277127925 1478755478541134744730743)
                      ·
                        rfl

theorem cell23_2879866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_2879866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879866 prefixEnd_2879866 := by exact prefixLift 2879866
  have htrace : WordTrace (prefixWord ++ tailWord_2879866) baseStart_2879866 baseEnd_2879866 := by
    simpa [prefixWord, tailWord_2879866, baseEnd_2879866] using wordTrace_append hprefix tailTrace_2879866
  have hstable : (prefixWord ++ tailWord_2879866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879866).length < 2 ^ (prefixWord ++ tailWord_2879866).sum := by decide
  have hdescent : baseEnd_2879866 < baseStart_2879866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879880 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2879880 : Nat := 118140960795 + 2879880 * 2 ^ 59
def prefixEnd_2879880 : Nat := 4983230072969 + 3 ^ 40 * 2879880 * 2
def baseEnd_2879880 : Nat := 1478762667270297689955679

theorem tailTrace_2879880 : CollatzResearch.WordTrace tailWord_2879880 prefixEnd_2879880 1478762667270297689955679 := by
  unfold tailWord_2879880
  simp only [CollatzResearch.WordTrace]
  refine ⟨52518926403347039595690547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70025235204462719460920729 52518926403347039595690547)
  ·
    refine ⟨78778389605020559393535821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52518926403347039595690547 78778389605020559393535821)
    ·
      refine ⟨29541896101882709772575933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78778389605020559393535821 29541896101882709772575933)
      ·
        refine ⟨11078211038206016164715975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29541896101882709772575933 11078211038206016164715975)
        ·
          refine ⟨16617316557309024247073963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078211038206016164715975 16617316557309024247073963)
          ·
            refine ⟨24925974835963536370610945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16617316557309024247073963 24925974835963536370610945)
            ·
              refine ⟨18694481126972652277958209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24925974835963536370610945 18694481126972652277958209)
              ·
                refine ⟨14020860845229489208468657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18694481126972652277958209 14020860845229489208468657)
                ·
                  refine ⟨10515645633922116906351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14020860845229489208468657 10515645633922116906351493)
                  ·
                    refine ⟨1971683556360396919940905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10515645633922116906351493 1971683556360396919940905)
                    ·
                      refine ⟨1478762667270297689955679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971683556360396919940905 1478762667270297689955679)
                      ·
                        rfl

theorem cell23_2879880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2879880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879880 prefixEnd_2879880 := by exact prefixLift 2879880
  have htrace : WordTrace (prefixWord ++ tailWord_2879880) baseStart_2879880 baseEnd_2879880 := by
    simpa [prefixWord, tailWord_2879880, baseEnd_2879880] using wordTrace_append hprefix tailTrace_2879880
  have hstable : (prefixWord ++ tailWord_2879880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879880).length < 2 ^ (prefixWord ++ tailWord_2879880).sum := by decide
  have hdescent : baseEnd_2879880 < baseStart_2879880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879903 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 6]
def baseStart_2879903 : Nat := 118140960795 + 2879903 * 2 ^ 59
def prefixEnd_2879903 : Nat := 4983230072969 + 3 ^ 40 * 2879903 * 2
def baseEnd_2879903 : Nat := 164308275258372344440897

theorem tailTrace_2879903 : CollatzResearch.WordTrace tailWord_2879903 prefixEnd_2879903 164308275258372344440897 := by
  unfold tailWord_2879903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105038691685610754119468363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70025794457073836079645575 105038691685610754119468363)
  ·
    refine ⟨157558037528416131179202545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105038691685610754119468363 157558037528416131179202545)
    ·
      refine ⟨118168528146312098384401909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157558037528416131179202545 118168528146312098384401909)
      ·
        refine ⟨11078299513716759223537679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118168528146312098384401909 11078299513716759223537679)
        ·
          refine ⟨16617449270575138835306519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078299513716759223537679 16617449270575138835306519)
          ·
            refine ⟨24926173905862708252959779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16617449270575138835306519 24926173905862708252959779)
            ·
              refine ⟨37389260858794062379439669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24926173905862708252959779 37389260858794062379439669)
              ·
                refine ⟨3505243205511943348072469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37389260858794062379439669 3505243205511943348072469)
                ·
                  refine ⟨164308275258372344440897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3505243205511943348072469 164308275258372344440897)
                  ·
                    rfl

theorem cell23_2879903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 6].length) (baseStart_2879903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879903 prefixEnd_2879903 := by exact prefixLift 2879903
  have htrace : WordTrace (prefixWord ++ tailWord_2879903) baseStart_2879903 baseEnd_2879903 := by
    simpa [prefixWord, tailWord_2879903, baseEnd_2879903] using wordTrace_append hprefix tailTrace_2879903
  have hstable : (prefixWord ++ tailWord_2879903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879903).length < 2 ^ (prefixWord ++ tailWord_2879903).sum := by decide
  have hdescent : baseEnd_2879903 < baseStart_2879903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879914 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2879914 : Nat := 118140960795 + 2879914 * 2 ^ 59
def prefixEnd_2879914 : Nat := 4983230072969 + 3 ^ 40 * 2879914 * 2
def baseEnd_2879914 : Nat := 1478780125612550556930523

theorem tailTrace_2879914 : CollatzResearch.WordTrace tailWord_2879914 prefixEnd_2879914 1478780125612550556930523 := by
  unfold tailWord_2879914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259773222142725749529699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70026061925713935332079197 26259773222142725749529699)
  ·
    refine ⟨39389659833214088624294549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26259773222142725749529699 39389659833214088624294549)
    ·
      refine ⟨1846390304681910404263807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39389659833214088624294549 1846390304681910404263807)
      ·
        refine ⟨2769585457022865606395711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1846390304681910404263807 2769585457022865606395711)
        ·
          refine ⟨4154378185534298409593567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769585457022865606395711 4154378185534298409593567)
          ·
            refine ⟨6231567278301447614390351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154378185534298409593567 6231567278301447614390351)
            ·
              refine ⟨9347350917452171421585527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231567278301447614390351 9347350917452171421585527)
              ·
                refine ⟨14021026376178257132378291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9347350917452171421585527 14021026376178257132378291)
                ·
                  refine ⟨21031539564267385698567437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14021026376178257132378291 21031539564267385698567437)
                  ·
                    refine ⟨7886827336600269636962789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21031539564267385698567437 7886827336600269636962789)
                    ·
                      refine ⟨1478780125612550556930523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7886827336600269636962789 1478780125612550556930523)
                      ·
                        rfl

theorem cell23_2879914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2879914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879914 prefixEnd_2879914 := by exact prefixLift 2879914
  have htrace : WordTrace (prefixWord ++ tailWord_2879914) baseStart_2879914 baseEnd_2879914 := by
    simpa [prefixWord, tailWord_2879914, baseEnd_2879914] using wordTrace_append hprefix tailTrace_2879914
  have hstable : (prefixWord ++ tailWord_2879914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879914).length < 2 ^ (prefixWord ++ tailWord_2879914).sum := by decide
  have hdescent : baseEnd_2879914 < baseStart_2879914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879917 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2879917 : Nat := 118140960795 + 2879917 * 2 ^ 59
def prefixEnd_2879917 : Nat := 4983230072969 + 3 ^ 40 * 2879917 * 2
def baseEnd_2879917 : Nat := 1478781666054514045193009

theorem tailTrace_2879917 : CollatzResearch.WordTrace tailWord_2879917 prefixEnd_2879917 1478781666054514045193009 := by
  unfold tailWord_2879917
  simp only [CollatzResearch.WordTrace]
  refine ⟨105039202307560034510478005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70026134871706689673652003 105039202307560034510478005)
  ·
    refine ⟨9847425216333753235357313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105039202307560034510478005 9847425216333753235357313)
    ·
      refine ⟨7385568912250314926517985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9847425216333753235357313 7385568912250314926517985)
      ·
        refine ⟨5539176684187736194888489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7385568912250314926517985 5539176684187736194888489)
        ·
          refine ⟨4154382513140802146166367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5539176684187736194888489 4154382513140802146166367)
          ·
            refine ⟨6231573769711203219249551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154382513140802146166367 6231573769711203219249551)
            ·
              refine ⟨9347360654566804828874327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231573769711203219249551 9347360654566804828874327)
              ·
                refine ⟨14021040981850207243311491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9347360654566804828874327 14021040981850207243311491)
                ·
                  refine ⟨21031561472775310864967237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14021040981850207243311491 21031561472775310864967237)
                  ·
                    refine ⟨3943417776145370787181357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21031561472775310864967237 3943417776145370787181357)
                    ·
                      refine ⟨1478781666054514045193009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943417776145370787181357 1478781666054514045193009)
                      ·
                        rfl

theorem cell23_2879917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2879917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879917 prefixEnd_2879917 := by exact prefixLift 2879917
  have htrace : WordTrace (prefixWord ++ tailWord_2879917) baseStart_2879917 baseEnd_2879917 := by
    simpa [prefixWord, tailWord_2879917, baseEnd_2879917] using wordTrace_append hprefix tailTrace_2879917
  have hstable : (prefixWord ++ tailWord_2879917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879917).length < 2 ^ (prefixWord ++ tailWord_2879917).sum := by decide
  have hdescent : baseEnd_2879917 < baseStart_2879917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879953 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2879953 : Nat := 118140960795 + 2879953 * 2 ^ 59
def prefixEnd_2879953 : Nat := 4983230072969 + 3 ^ 40 * 2879953 * 2
def baseEnd_2879953 : Nat := 1478800151358075904342843

theorem tailTrace_2879953 : CollatzResearch.WordTrace tailWord_2879953 prefixEnd_2879953 1478800151358075904342843 := by
  unfold tailWord_2879953
  simp only [CollatzResearch.WordTrace]
  refine ⟨105040515335429612658788513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70027010223619741772525675 105040515335429612658788513)
  ·
    refine ⟨78780386501572209494091385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105040515335429612658788513 78780386501572209494091385)
    ·
      refine ⟨59085289876179157120568539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78780386501572209494091385 59085289876179157120568539)
      ·
        refine ⟨88627934814268735680852809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59085289876179157120568539 88627934814268735680852809)
        ·
          refine ⟨66470951110701551760639607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88627934814268735680852809 66470951110701551760639607)
          ·
            refine ⟨99706426666052327640959411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66470951110701551760639607 99706426666052327640959411)
            ·
              refine ⟨149559639999078491461439117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99706426666052327640959411 149559639999078491461439117)
              ·
                refine ⟨56084864999654434298039669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149559639999078491461439117 56084864999654434298039669)
                ·
                  refine ⟨5257956093717603215441219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56084864999654434298039669 5257956093717603215441219)
                  ·
                    refine ⟨7886934140576404823161829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257956093717603215441219 7886934140576404823161829)
                    ·
                      refine ⟨1478800151358075904342843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7886934140576404823161829 1478800151358075904342843)
                      ·
                        rfl

theorem cell23_2879953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2879953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879953 prefixEnd_2879953 := by exact prefixLift 2879953
  have htrace : WordTrace (prefixWord ++ tailWord_2879953) baseStart_2879953 baseEnd_2879953 := by
    simpa [prefixWord, tailWord_2879953, baseEnd_2879953] using wordTrace_append hprefix tailTrace_2879953
  have hstable : (prefixWord ++ tailWord_2879953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879953).length < 2 ^ (prefixWord ++ tailWord_2879953).sum := by decide
  have hdescent : baseEnd_2879953 < baseStart_2879953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879954 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_2879954 : Nat := 118140960795 + 2879954 * 2 ^ 59
def prefixEnd_2879954 : Nat := 4983230072969 + 3 ^ 40 * 2879954 * 2
def baseEnd_2879954 : Nat := 164311184982081155603371

theorem tailTrace_2879954 : CollatzResearch.WordTrace tailWord_2879954 prefixEnd_2879954 164311184982081155603371 := by
  unfold tailWord_2879954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26260137952106497457393729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70027034538950659886383277 26260137952106497457393729)
  ·
    refine ⟨19695103464079873093045297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26260137952106497457393729 19695103464079873093045297)
    ·
      refine ⟨14771327598059904819783973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19695103464079873093045297 14771327598059904819783973)
      ·
        refine ⟨2769623924636232153709495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14771327598059904819783973 2769623924636232153709495)
        ·
          refine ⟨4154435886954348230564243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769623924636232153709495 4154435886954348230564243)
          ·
            refine ⟨6231653830431522345846365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154435886954348230564243 6231653830431522345846365)
            ·
              refine ⟨2336870186411820879692387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6231653830431522345846365 2336870186411820879692387)
              ·
                refine ⟨3505305279617731319538581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336870186411820879692387 3505305279617731319538581)
                ·
                  refine ⟨164311184982081155603371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3505305279617731319538581 164311184982081155603371)
                  ·
                    rfl

theorem cell23_2879954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_2879954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879954 prefixEnd_2879954 := by exact prefixLift 2879954
  have htrace : WordTrace (prefixWord ++ tailWord_2879954) baseStart_2879954 baseEnd_2879954 := by
    simpa [prefixWord, tailWord_2879954, baseEnd_2879954] using wordTrace_append hprefix tailTrace_2879954
  have hstable : (prefixWord ++ tailWord_2879954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879954).length < 2 ^ (prefixWord ++ tailWord_2879954).sum := by decide
  have hdescent : baseEnd_2879954 < baseStart_2879954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879981 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2879981 : Nat := 118140960795 + 2879981 * 2 ^ 59
def prefixEnd_2879981 : Nat := 4983230072969 + 3 ^ 40 * 2879981 * 2
def baseEnd_2879981 : Nat := 1478814528816401794792715

theorem tailTrace_2879981 : CollatzResearch.WordTrace tailWord_2879981 prefixEnd_2879981 1478814528816401794792715 := by
  unfold tailWord_2879981
  simp only [CollatzResearch.WordTrace]
  refine ⟨105041536579328173440807797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70027691052885448960538531 105041536579328173440807797)
  ·
    refine ⟨9847644054312016260075731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105041536579328173440807797 9847644054312016260075731)
    ·
      refine ⟨14771466081468024390113597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9847644054312016260075731 14771466081468024390113597)
      ·
        refine ⟨5539299780550509146292599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14771466081468024390113597 5539299780550509146292599)
        ·
          refine ⟨8308949670825763719438899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539299780550509146292599 8308949670825763719438899)
          ·
            refine ⟨12463424506238645579158349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308949670825763719438899 12463424506238645579158349)
            ·
              refine ⟨4673784189839492092184381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12463424506238645579158349 4673784189839492092184381)
              ·
                refine ⟨1752669071189809534569143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4673784189839492092184381 1752669071189809534569143)
                ·
                  refine ⟨2629003606784714301853715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752669071189809534569143 2629003606784714301853715)
                  ·
                    refine ⟨3943505410177071452780573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629003606784714301853715 3943505410177071452780573)
                    ·
                      refine ⟨1478814528816401794792715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943505410177071452780573 1478814528816401794792715)
                      ·
                        rfl

theorem cell23_2879981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2879981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879981 prefixEnd_2879981 := by exact prefixLift 2879981
  have htrace : WordTrace (prefixWord ++ tailWord_2879981) baseStart_2879981 baseEnd_2879981 := by
    simpa [prefixWord, tailWord_2879981, baseEnd_2879981] using wordTrace_append hprefix tailTrace_2879981
  have hstable : (prefixWord ++ tailWord_2879981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879981).length < 2 ^ (prefixWord ++ tailWord_2879981).sum := by decide
  have hdescent : baseEnd_2879981 < baseStart_2879981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879983 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_2879983 : Nat := 118140960795 + 2879983 * 2 ^ 59
def prefixEnd_2879983 : Nat := 4983230072969 + 3 ^ 40 * 2879983 * 2
def baseEnd_2879983 : Nat := 1478815555777710786967705

theorem tailTrace_2879983 : CollatzResearch.WordTrace tailWord_2879983 prefixEnd_2879983 1478815555777710786967705 := by
  unfold tailWord_2879983
  simp only [CollatzResearch.WordTrace]
  refine ⟨105041609525320927782380603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70027739683547285188253735 105041609525320927782380603)
  ·
    refine ⟨157562414287981391673570905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105041609525320927782380603 157562414287981391673570905)
    ·
      refine ⟨118171810715986043755178179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157562414287981391673570905 118171810715986043755178179)
      ·
        refine ⟨177257716073979065632767269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118171810715986043755178179 177257716073979065632767269)
        ·
          refine ⟨33235821763871074806143863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177257716073979065632767269 33235821763871074806143863)
          ·
            refine ⟨49853732645806612209215795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33235821763871074806143863 49853732645806612209215795)
            ·
              refine ⟨74780598968709918313823693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49853732645806612209215795 74780598968709918313823693)
              ·
                refine ⟨28042724613266219367683885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74780598968709918313823693 28042724613266219367683885)
                ·
                  refine ⟨10516021729974832262881457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28042724613266219367683885 10516021729974832262881457)
                  ·
                    refine ⟨7887016297481124197161093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10516021729974832262881457 7887016297481124197161093)
                    ·
                      refine ⟨1478815555777710786967705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7887016297481124197161093 1478815555777710786967705)
                      ·
                        rfl

theorem cell23_2879983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_2879983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2879983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2879983 prefixEnd_2879983 := by exact prefixLift 2879983
  have htrace : WordTrace (prefixWord ++ tailWord_2879983) baseStart_2879983 baseEnd_2879983 := by
    simpa [prefixWord, tailWord_2879983, baseEnd_2879983] using wordTrace_append hprefix tailTrace_2879983
  have hstable : (prefixWord ++ tailWord_2879983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879983).length < 2 ^ (prefixWord ++ tailWord_2879983).sum := by decide
  have hdescent : baseEnd_2879983 < baseStart_2879983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880014 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_2880014 : Nat := 118140960795 + 2880014 * 2 ^ 59
def prefixEnd_2880014 : Nat := 4983230072969 + 3 ^ 40 * 2880014 * 2
def baseEnd_2880014 : Nat := 492943824559333388560021

theorem tailTrace_2880014 : CollatzResearch.WordTrace tailWord_2880014 prefixEnd_2880014 492943824559333388560021 := by
  unfold tailWord_2880014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130342523526077509594887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70028493458805746717839397 13130342523526077509594887)
  ·
    refine ⟨19695513785289116264392331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13130342523526077509594887 19695513785289116264392331)
    ·
      refine ⟨29543270677933674396588497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19695513785289116264392331 29543270677933674396588497)
      ·
        refine ⟨22157453008450255797441373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29543270677933674396588497 22157453008450255797441373)
        ·
          refine ⟨8309044878168845924040515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22157453008450255797441373 8309044878168845924040515)
          ·
            refine ⟨12463567317253268886060773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309044878168845924040515 12463567317253268886060773)
            ·
              refine ⟨2336918871984987916136395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12463567317253268886060773 2336918871984987916136395)
              ·
                refine ⟨3505378307977481874204593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336918871984987916136395 3505378307977481874204593)
                ·
                  refine ⟨2629033730983111405653445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505378307977481874204593 2629033730983111405653445)
                  ·
                    refine ⟨492943824559333388560021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629033730983111405653445 492943824559333388560021)
                    ·
                      rfl

theorem cell23_2880014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_2880014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880014 prefixEnd_2880014 := by exact prefixLift 2880014
  have htrace : WordTrace (prefixWord ++ tailWord_2880014) baseStart_2880014 baseEnd_2880014 := by
    simpa [prefixWord, tailWord_2880014, baseEnd_2880014] using wordTrace_append hprefix tailTrace_2880014
  have hstable : (prefixWord ++ tailWord_2880014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880014).length < 2 ^ (prefixWord ++ tailWord_2880014).sum := by decide
  have hdescent : baseEnd_2880014 < baseStart_2880014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880024 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2880024 : Nat := 118140960795 + 2880024 * 2 ^ 59
def prefixEnd_2880024 : Nat := 4983230072969 + 3 ^ 40 * 2880024 * 2
def baseEnd_2880024 : Nat := 1478836608484545126555017

theorem tailTrace_2880024 : CollatzResearch.WordTrace tailWord_2880024 prefixEnd_2880024 1478836608484545126555017 := by
  unfold tailWord_2880024
  simp only [CollatzResearch.WordTrace]
  refine ⟨52521552459086195892311563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70028736612114927856415417 52521552459086195892311563)
  ·
    refine ⟨78782328688629293838467345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52521552459086195892311563 78782328688629293838467345)
    ·
      refine ⟨59086746516471970378850509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78782328688629293838467345 59086746516471970378850509)
      ·
        refine ⟨22157529943676988892068941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59086746516471970378850509 22157529943676988892068941)
        ·
          refine ⟨8309073728878870834525853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22157529943676988892068941 8309073728878870834525853)
          ·
            refine ⟨3115902648329576562947195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8309073728878870834525853 3115902648329576562947195)
            ·
              refine ⟨4673853972494364844420793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115902648329576562947195 4673853972494364844420793)
              ·
                refine ⟨3505390479370773633315595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673853972494364844420793 3505390479370773633315595)
                ·
                  refine ⟨5258085719056160449973393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505390479370773633315595 5258085719056160449973393)
                  ·
                    refine ⟨3943564289292120337480045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258085719056160449973393 3943564289292120337480045)
                    ·
                      refine ⟨1478836608484545126555017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943564289292120337480045 1478836608484545126555017)
                      ·
                        rfl

theorem cell23_2880024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2880024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880024 prefixEnd_2880024 := by exact prefixLift 2880024
  have htrace : WordTrace (prefixWord ++ tailWord_2880024) baseStart_2880024 baseEnd_2880024 := by
    simpa [prefixWord, tailWord_2880024, baseEnd_2880024] using wordTrace_append hprefix tailTrace_2880024
  have hstable : (prefixWord ++ tailWord_2880024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880024).length < 2 ^ (prefixWord ++ tailWord_2880024).sum := by decide
  have hdescent : baseEnd_2880024 < baseStart_2880024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880043 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_2880043 : Nat := 118140960795 + 2880043 * 2 ^ 59
def prefixEnd_2880043 : Nat := 4983230072969 + 3 ^ 40 * 2880043 * 2
def baseEnd_2880043 : Nat := 1478846364616980552217429

theorem tailTrace_2880043 : CollatzResearch.WordTrace tailWord_2880043 prefixEnd_2880043 1478846364616980552217429 := by
  unfold tailWord_2880043
  simp only [CollatzResearch.WordTrace]
  refine ⟨105043797905103558029564783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70029198603402372019709855 105043797905103558029564783)
  ·
    refine ⟨157565696857655337044347175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105043797905103558029564783 157565696857655337044347175)
    ·
      refine ⟨236348545286483005566520763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157565696857655337044347175 236348545286483005566520763)
      ·
        refine ⟨354522817929724508349781145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236348545286483005566520763 354522817929724508349781145)
        ·
          refine ⟨265892113447293381262335859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354522817929724508349781145 265892113447293381262335859)
          ·
            refine ⟨398838170170940071893503789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265892113447293381262335859 398838170170940071893503789)
            ·
              refine ⟨149564313814102526960063921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398838170170940071893503789 149564313814102526960063921)
              ·
                refine ⟨112173235360576895220047941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149564313814102526960063921 112173235360576895220047941)
                ·
                  refine ⟨21032481630108167853758989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112173235360576895220047941 21032481630108167853758989)
                  ·
                    refine ⟨7887180611290562945159621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21032481630108167853758989 7887180611290562945159621)
                    ·
                      refine ⟨1478846364616980552217429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7887180611290562945159621 1478846364616980552217429)
                      ·
                        rfl

theorem cell23_2880043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_2880043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880043 prefixEnd_2880043 := by exact prefixLift 2880043
  have htrace : WordTrace (prefixWord ++ tailWord_2880043) baseStart_2880043 baseEnd_2880043 := by
    simpa [prefixWord, tailWord_2880043, baseEnd_2880043] using wordTrace_append hprefix tailTrace_2880043
  have hstable : (prefixWord ++ tailWord_2880043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880043).length < 2 ^ (prefixWord ++ tailWord_2880043).sum := by decide
  have hdescent : baseEnd_2880043 < baseStart_2880043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880060 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2880060 : Nat := 118140960795 + 2880060 * 2 ^ 59
def prefixEnd_2880060 : Nat := 4983230072969 + 3 ^ 40 * 2880060 * 2
def baseEnd_2880060 : Nat := 1478855093788106985704851

theorem tailTrace_2880060 : CollatzResearch.WordTrace tailWord_2880060 prefixEnd_2880060 1478855093788106985704851 := by
  unfold tailWord_2880060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52522208973020984966466817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70029611964027979955289089 52522208973020984966466817)
  ·
    refine ⟨39391656729765738724850113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52522208973020984966466817 39391656729765738724850113)
    ·
      refine ⟨29543742547324304043637585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39391656729765738724850113 29543742547324304043637585)
      ·
        refine ⟨22157806910493228032728189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29543742547324304043637585 22157806910493228032728189)
        ·
          refine ⟨8309177591434960512273071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22157806910493228032728189 8309177591434960512273071)
          ·
            refine ⟨12463766387152440768409607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309177591434960512273071 12463766387152440768409607)
            ·
              refine ⟨18695649580728661152614411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12463766387152440768409607 18695649580728661152614411)
              ·
                refine ⟨28043474371092991728921617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18695649580728661152614411 28043474371092991728921617)
                ·
                  refine ⟨21032605778319743796691213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28043474371092991728921617 21032605778319743796691213)
                  ·
                    refine ⟨7887227166869903923759205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21032605778319743796691213 7887227166869903923759205)
                    ·
                      refine ⟨1478855093788106985704851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7887227166869903923759205 1478855093788106985704851)
                      ·
                        rfl

theorem cell23_2880060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2880060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880060 prefixEnd_2880060 := by exact prefixLift 2880060
  have htrace : WordTrace (prefixWord ++ tailWord_2880060) baseStart_2880060 baseEnd_2880060 := by
    simpa [prefixWord, tailWord_2880060, baseEnd_2880060] using wordTrace_append hprefix tailTrace_2880060
  have hstable : (prefixWord ++ tailWord_2880060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880060).length < 2 ^ (prefixWord ++ tailWord_2880060).sum := by decide
  have hdescent : baseEnd_2880060 < baseStart_2880060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880098 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2880098 : Nat := 118140960795 + 2880098 * 2 ^ 59
def prefixEnd_2880098 : Nat := 4983230072969 + 3 ^ 40 * 2880098 * 2
def baseEnd_2880098 : Nat := 1478874606052977837029677

theorem tailTrace_2880098 : CollatzResearch.WordTrace tailWord_2880098 prefixEnd_2880098 1478874606052977837029677 := by
  unfold tailWord_2880098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26261450979976075605704237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70030535946602868281877965 26261450979976075605704237)
  ·
    refine ⟨9848044117491028352139089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26261450979976075605704237 9848044117491028352139089)
    ·
      refine ⟨7386033088118271264104317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9848044117491028352139089 7386033088118271264104317)
      ·
        refine ⟨2769762408044351724039119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7386033088118271264104317 2769762408044351724039119)
        ·
          refine ⟨4154643612066527586058679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769762408044351724039119 4154643612066527586058679)
          ·
            refine ⟨6231965418099791379088019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154643612066527586058679 6231965418099791379088019)
            ·
              refine ⟨9347948127149687068632029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231965418099791379088019 9347948127149687068632029)
              ·
                refine ⟨3505480547681132650737011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9347948127149687068632029 3505480547681132650737011)
                ·
                  refine ⟨5258220821521698976105517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505480547681132650737011 5258220821521698976105517)
                  ·
                    refine ⟨1971832808070637116039569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5258220821521698976105517 1971832808070637116039569)
                    ·
                      refine ⟨1478874606052977837029677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1971832808070637116039569 1478874606052977837029677)
                      ·
                        rfl

theorem cell23_2880098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2880098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880098 prefixEnd_2880098 := by exact prefixLift 2880098
  have htrace : WordTrace (prefixWord ++ tailWord_2880098) baseStart_2880098 baseEnd_2880098 := by
    simpa [prefixWord, tailWord_2880098, baseEnd_2880098] using wordTrace_append hprefix tailTrace_2880098
  have hstable : (prefixWord ++ tailWord_2880098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880098).length < 2 ^ (prefixWord ++ tailWord_2880098).sum := by decide
  have hdescent : baseEnd_2880098 < baseStart_2880098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880174 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2880174 : Nat := 118140960795 + 2880174 * 2 ^ 59
def prefixEnd_2880174 : Nat := 4983230072969 + 3 ^ 40 * 2880174 * 2
def baseEnd_2880174 : Nat := 1478913630582719539679327

theorem tailTrace_2880174 : CollatzResearch.WordTrace tailWord_2880174 prefixEnd_2880174 1478913630582719539679327 := by
  unfold tailWord_2880174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131071983453620925322947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70032383911752644935055717 13131071983453620925322947)
  ·
    refine ⟨19696607975180431387984421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13131071983453620925322947 19696607975180431387984421)
    ·
      refine ⟨3693113995346330885247079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19696607975180431387984421 3693113995346330885247079)
      ·
        refine ⟨5539670993019496327870619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693113995346330885247079 5539670993019496327870619)
        ·
          refine ⟨8309506489529244491805929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539670993019496327870619 8309506489529244491805929)
          ·
            refine ⟨6232129867146933368854447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8309506489529244491805929 6232129867146933368854447)
            ·
              refine ⟨9348194800720400053281671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232129867146933368854447 9348194800720400053281671)
              ·
                refine ⟨14022292201080600079922507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9348194800720400053281671 14022292201080600079922507)
                ·
                  refine ⟨21033438301620900119883761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14022292201080600079922507 21033438301620900119883761)
                  ·
                    refine ⟨15775078726215675089912821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21033438301620900119883761 15775078726215675089912821)
                    ·
                      refine ⟨1478913630582719539679327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15775078726215675089912821 1478913630582719539679327)
                      ·
                        rfl

theorem cell23_2880174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2880174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880174 prefixEnd_2880174 := by exact prefixLift 2880174
  have htrace : WordTrace (prefixWord ++ tailWord_2880174) baseStart_2880174 baseEnd_2880174 := by
    simpa [prefixWord, tailWord_2880174, baseEnd_2880174] using wordTrace_append hprefix tailTrace_2880174
  have hstable : (prefixWord ++ tailWord_2880174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880174).length < 2 ^ (prefixWord ++ tailWord_2880174).sum := by decide
  have hdescent : baseEnd_2880174 < baseStart_2880174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880198 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2880198 : Nat := 118140960795 + 2880198 * 2 ^ 59
def prefixEnd_2880198 : Nat := 4983230072969 + 3 ^ 40 * 2880198 * 2
def baseEnd_2880198 : Nat := 492975318039475815259739

theorem tailTrace_2880198 : CollatzResearch.WordTrace tailWord_2880198 prefixEnd_2880198 492975318039475815259739 := by
  unfold tailWord_2880198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282795350610688109420539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70032967479694679667638165 3282795350610688109420539)
  ·
    refine ⟨4924193025916032164130809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3282795350610688109420539 4924193025916032164130809)
    ·
      refine ⟨3693144769437024123098107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4924193025916032164130809 3693144769437024123098107)
      ·
        refine ⟨5539717154155536184647161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693144769437024123098107 5539717154155536184647161)
        ·
          refine ⟨4154787865616652138485371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5539717154155536184647161 4154787865616652138485371)
          ·
            refine ⟨6232181798424978207728057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154787865616652138485371 6232181798424978207728057)
            ·
              refine ⟨4674136348818733655796043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232181798424978207728057 4674136348818733655796043)
              ·
                refine ⟨7011204523228100483694065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674136348818733655796043 7011204523228100483694065)
                ·
                  refine ⟨5258403392421075362770549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7011204523228100483694065 5258403392421075362770549)
                  ·
                    refine ⟨492975318039475815259739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5258403392421075362770549 492975318039475815259739)
                    ·
                      rfl

theorem cell23_2880198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2880198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880198 prefixEnd_2880198 := by exact prefixLift 2880198
  have htrace : WordTrace (prefixWord ++ tailWord_2880198) baseStart_2880198 baseEnd_2880198 := by
    simpa [prefixWord, tailWord_2880198, baseEnd_2880198] using wordTrace_append hprefix tailTrace_2880198
  have hstable : (prefixWord ++ tailWord_2880198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880198).length < 2 ^ (prefixWord ++ tailWord_2880198).sum := by decide
  have hdescent : baseEnd_2880198 < baseStart_2880198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880204 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2880204 : Nat := 118140960795 + 2880204 * 2 ^ 59
def prefixEnd_2880204 : Nat := 4983230072969 + 3 ^ 40 * 2880204 * 2
def baseEnd_2880204 : Nat := 1478929035002354422304189

theorem tailTrace_2880204 : CollatzResearch.WordTrace tailWord_2880204 prefixEnd_2880204 1478929035002354422304189 := by
  unfold tailWord_2880204
  simp only [CollatzResearch.WordTrace]
  refine ⟨52524835028760141263087833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70033113371680188350783777 52524835028760141263087833)
  ·
    refine ⟨39393626271570105947315875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52524835028760141263087833 39393626271570105947315875)
    ·
      refine ⟨59090439407355158920973813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39393626271570105947315875 59090439407355158920973813)
      ·
        refine ⟨5539728694439546148841295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59090439407355158920973813 5539728694439546148841295)
        ·
          refine ⟨8309593041659319223261943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539728694439546148841295 8309593041659319223261943)
          ·
            refine ⟨12464389562488978834892915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309593041659319223261943 12464389562488978834892915)
            ·
              refine ⟨18696584343733468252339373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12464389562488978834892915 18696584343733468252339373)
              ·
                refine ⟨7011219128900050594627265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18696584343733468252339373 7011219128900050594627265)
                ·
                  refine ⟨5258414346675037945970449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7011219128900050594627265 5258414346675037945970449)
                  ·
                    refine ⟨3943810760006278459477837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258414346675037945970449 3943810760006278459477837)
                    ·
                      refine ⟨1478929035002354422304189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943810760006278459477837 1478929035002354422304189)
                      ·
                        rfl

theorem cell23_2880204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2880204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880204 prefixEnd_2880204 := by exact prefixLift 2880204
  have htrace : WordTrace (prefixWord ++ tailWord_2880204) baseStart_2880204 baseEnd_2880204 := by
    simpa [prefixWord, tailWord_2880204, baseEnd_2880204] using wordTrace_append hprefix tailTrace_2880204
  have hstable : (prefixWord ++ tailWord_2880204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880204).length < 2 ^ (prefixWord ++ tailWord_2880204).sum := by decide
  have hdescent : baseEnd_2880204 < baseStart_2880204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880228 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_2880228 : Nat := 118140960795 + 2880228 * 2 ^ 59
def prefixEnd_2880228 : Nat := 4983230072969 + 3 ^ 40 * 2880228 * 2
def baseEnd_2880228 : Nat := 492980452846020776134693

theorem tailTrace_2880228 : CollatzResearch.WordTrace tailWord_2880228 prefixEnd_2880228 492980452846020776134693 := by
  unfold tailWord_2880228
  simp only [CollatzResearch.WordTrace]
  refine ⟨52525272704716667312524669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70033696939622223083366225 52525272704716667312524669)
  ·
    refine ⟨19696977264268750242196751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52525272704716667312524669 19696977264268750242196751)
    ·
      refine ⟨29545465896403125363295127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19696977264268750242196751 29545465896403125363295127)
      ·
        refine ⟨44318198844604688044942691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29545465896403125363295127 44318198844604688044942691)
        ·
          refine ⟨66477298266907032067414037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44318198844604688044942691 66477298266907032067414037)
          ·
            refine ⟨3116123356261267128160033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66477298266907032067414037 3116123356261267128160033)
            ·
              refine ⟨2337092517195950346120025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116123356261267128160033 2337092517195950346120025)
              ·
                refine ⟨1752819387896962759590019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337092517195950346120025 1752819387896962759590019)
                ·
                  refine ⟨2629229081845444139385029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752819387896962759590019 2629229081845444139385029)
                  ·
                    refine ⟨492980452846020776134693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629229081845444139385029 492980452846020776134693)
                    ·
                      rfl

theorem cell23_2880228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_2880228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880228 prefixEnd_2880228 := by exact prefixLift 2880228
  have htrace : WordTrace (prefixWord ++ tailWord_2880228) baseStart_2880228 baseEnd_2880228 := by
    simpa [prefixWord, tailWord_2880228, baseEnd_2880228] using wordTrace_append hprefix tailTrace_2880228
  have hstable : (prefixWord ++ tailWord_2880228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880228).length < 2 ^ (prefixWord ++ tailWord_2880228).sum := by decide
  have hdescent : baseEnd_2880228 < baseStart_2880228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880234 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_2880234 : Nat := 118140960795 + 2880234 * 2 ^ 59
def prefixEnd_2880234 : Nat := 4983230072969 + 3 ^ 40 * 2880234 * 2
def baseEnd_2880234 : Nat := 1478944439421989304929051

theorem tailTrace_2880234 : CollatzResearch.WordTrace tailWord_2880234 prefixEnd_2880234 1478944439421989304929051 := by
  unfold tailWord_2880234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26262691061852899412441939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70033842831607731766511837 26262691061852899412441939)
  ·
    refine ⟨39394036592779349118662909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26262691061852899412441939 39394036592779349118662909)
    ·
      refine ⟨14772763722292255919498591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39394036592779349118662909 14772763722292255919498591)
      ·
        refine ⟨22159145583438383879247887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772763722292255919498591 22159145583438383879247887)
        ·
          refine ⟨33238718375157575818871831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22159145583438383879247887 33238718375157575818871831)
          ·
            refine ⟨49858077562736363728307747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33238718375157575818871831 49858077562736363728307747)
            ·
              refine ⟨74787116344104545592461621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49858077562736363728307747 74787116344104545592461621)
              ·
                refine ⟨7011292157259801149293277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74787116344104545592461621 7011292157259801149293277)
                ·
                  refine ⟨2629234558972425430984979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7011292157259801149293277 2629234558972425430984979)
                  ·
                    refine ⟨3943851838458638146477469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629234558972425430984979 3943851838458638146477469)
                    ·
                      refine ⟨1478944439421989304929051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943851838458638146477469 1478944439421989304929051)
                      ·
                        rfl

theorem cell23_2880234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_2880234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880234 prefixEnd_2880234 := by exact prefixLift 2880234
  have htrace : WordTrace (prefixWord ++ tailWord_2880234) baseStart_2880234 baseEnd_2880234 := by
    simpa [prefixWord, tailWord_2880234, baseEnd_2880234] using wordTrace_append hprefix tailTrace_2880234
  have hstable : (prefixWord ++ tailWord_2880234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880234).length < 2 ^ (prefixWord ++ tailWord_2880234).sum := by decide
  have hdescent : baseEnd_2880234 < baseStart_2880234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880237 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2880237 : Nat := 118140960795 + 2880237 * 2 ^ 59
def prefixEnd_2880237 : Nat := 4983230072969 + 3 ^ 40 * 2880237 * 2
def baseEnd_2880237 : Nat := 492981993287984264397179

theorem tailTrace_2880237 : CollatzResearch.WordTrace tailWord_2880237 prefixEnd_2880237 492981993287984264397179 := by
  unfold tailWord_2880237
  simp only [CollatzResearch.WordTrace]
  refine ⟨105050873666400729162126965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70033915777600486108084643 105050873666400729162126965)
  ·
    refine ⟨9848519406225068358949403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105050873666400729162126965 9848519406225068358949403)
    ·
      refine ⟨14772779109337602538424105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848519406225068358949403 14772779109337602538424105)
      ·
        refine ⟨11079584332003201903818079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14772779109337602538424105 11079584332003201903818079)
        ·
          refine ⟨16619376498004802855727119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11079584332003201903818079 16619376498004802855727119)
          ·
            refine ⟨24929064747007204283590679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16619376498004802855727119 24929064747007204283590679)
            ·
              refine ⟨37393597120510806425386019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24929064747007204283590679 37393597120510806425386019)
              ·
                refine ⟨56090395680766209638079029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37393597120510806425386019 56090395680766209638079029)
                ·
                  refine ⟨5258474595071832153569909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56090395680766209638079029 5258474595071832153569909)
                  ·
                    refine ⟨492981993287984264397179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5258474595071832153569909 492981993287984264397179)
                    ·
                      rfl

theorem cell23_2880237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2880237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880237 prefixEnd_2880237 := by exact prefixLift 2880237
  have htrace : WordTrace (prefixWord ++ tailWord_2880237) baseStart_2880237 baseEnd_2880237 := by
    simpa [prefixWord, tailWord_2880237, baseEnd_2880237] using wordTrace_append hprefix tailTrace_2880237
  have hstable : (prefixWord ++ tailWord_2880237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880237).length < 2 ^ (prefixWord ++ tailWord_2880237).sum := by decide
  have hdescent : baseEnd_2880237 < baseStart_2880237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880254 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2880254 : Nat := 118140960795 + 2880254 * 2 ^ 59
def prefixEnd_2880254 : Nat := 4983230072969 + 3 ^ 40 * 2880254 * 2
def baseEnd_2880254 : Nat := 492984903011693075559653

theorem tailTrace_2880254 : CollatzResearch.WordTrace tailWord_2880254 prefixEnd_2880254 492984903011693075559653 := by
  unfold tailWord_2880254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131436713417392633186977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70034329138226094043663877 13131436713417392633186977)
  ·
    refine ⟨9848577535063044474890233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13131436713417392633186977 9848577535063044474890233)
    ·
      refine ⟨7386433151297283356167675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9848577535063044474890233 7386433151297283356167675)
      ·
        refine ⟨11079649726945925034251513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386433151297283356167675 11079649726945925034251513)
        ·
          refine ⟨8309737295209443775688635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11079649726945925034251513 8309737295209443775688635)
          ·
            refine ⟨12464605942814165663532953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309737295209443775688635 12464605942814165663532953)
            ·
              refine ⟨9348454457110624247649715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12464605942814165663532953 9348454457110624247649715)
              ·
                refine ⟨14022681685665936371474573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9348454457110624247649715 14022681685665936371474573)
                ·
                  refine ⟨5258505632124726139302965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14022681685665936371474573 5258505632124726139302965)
                  ·
                    refine ⟨492984903011693075559653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5258505632124726139302965 492984903011693075559653)
                    ·
                      rfl

theorem cell23_2880254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2880254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880254 prefixEnd_2880254 := by exact prefixLift 2880254
  have htrace : WordTrace (prefixWord ++ tailWord_2880254) baseStart_2880254 baseEnd_2880254 := by
    simpa [prefixWord, tailWord_2880254, baseEnd_2880254] using wordTrace_append hprefix tailTrace_2880254
  have hstable : (prefixWord ++ tailWord_2880254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880254).length < 2 ^ (prefixWord ++ tailWord_2880254).sum := by decide
  have hdescent : baseEnd_2880254 < baseStart_2880254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880267 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 4, 4]
def baseStart_2880267 : Nat := 118140960795 + 2880267 * 2 ^ 59
def prefixEnd_2880267 : Nat := 4983230072969 + 3 ^ 40 * 2880267 * 2
def baseEnd_2880267 : Nat := 492987128094529225272133

theorem tailTrace_2880267 : CollatzResearch.WordTrace tailWord_2880267 prefixEnd_2880267 492987128094529225272133 := by
  unfold tailWord_2880267
  simp only [CollatzResearch.WordTrace]
  refine ⟨105051967856292044285719055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70034645237528029523812703 105051967856292044285719055)
  ·
    refine ⟨157577951784438066428578583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105051967856292044285719055 157577951784438066428578583)
    ·
      refine ⟨236366927676657099642867875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157577951784438066428578583 236366927676657099642867875)
      ·
        refine ⟨354550391514985649464301813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236366927676657099642867875 354550391514985649464301813)
        ·
          refine ⟨33239099204529904637278295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354550391514985649464301813 33239099204529904637278295)
          ·
            refine ⟨49858648806794856955917443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33239099204529904637278295 49858648806794856955917443)
            ·
              refine ⟨74787973210192285433876165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49858648806794856955917443 74787973210192285433876165)
              ·
                refine ⟨14022744976911053518851781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74787973210192285433876165 14022744976911053518851781)
                ·
                  refine ⟨2629264683170822534784709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14022744976911053518851781 2629264683170822534784709)
                  ·
                    refine ⟨492987128094529225272133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629264683170822534784709 492987128094529225272133)
                    ·
                      rfl

theorem cell23_2880267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 4].length) (baseStart_2880267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880267 prefixEnd_2880267 := by exact prefixLift 2880267
  have htrace : WordTrace (prefixWord ++ tailWord_2880267) baseStart_2880267 baseEnd_2880267 := by
    simpa [prefixWord, tailWord_2880267, baseEnd_2880267] using wordTrace_append hprefix tailTrace_2880267
  have hstable : (prefixWord ++ tailWord_2880267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880267).length < 2 ^ (prefixWord ++ tailWord_2880267).sum := by decide
  have hdescent : baseEnd_2880267 < baseStart_2880267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880277 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2880277 : Nat := 118140960795 + 2880277 * 2 ^ 59
def prefixEnd_2880277 : Nat := 4983230072969 + 3 ^ 40 * 2880277 * 2
def baseEnd_2880277 : Nat := 1478966519090132636691353

theorem tailTrace_2880277 : CollatzResearch.WordTrace tailWord_2880277 prefixEnd_2880277 1478966519090132636691353 := by
  unfold tailWord_2880277
  simp only [CollatzResearch.WordTrace]
  refine ⟨105052332586255815993583085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70034888390837210662388723 105052332586255815993583085)
  ·
    refine ⟨39394624719845930997593657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105052332586255815993583085 39394624719845930997593657)
    ·
      refine ⟨29545968539884448248195243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39394624719845930997593657 29545968539884448248195243)
      ·
        refine ⟨44318952809826672372292865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29545968539884448248195243 44318952809826672372292865)
        ·
          refine ⟨33239214607370004279219649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44318952809826672372292865 33239214607370004279219649)
          ·
            refine ⟨24929410955527503209414737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33239214607370004279219649 24929410955527503209414737)
            ·
              refine ⟨18697058216645627407061053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24929410955527503209414737 18697058216645627407061053)
              ·
                refine ⟨7011396831242110277647895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18697058216645627407061053 7011396831242110277647895)
                ·
                  refine ⟨10517095246863165416471843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7011396831242110277647895 10517095246863165416471843)
                  ·
                    refine ⟨15775642870294748124707765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10517095246863165416471843 15775642870294748124707765)
                    ·
                      refine ⟨1478966519090132636691353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15775642870294748124707765 1478966519090132636691353)
                      ·
                        rfl

theorem cell23_2880277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2880277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880277 prefixEnd_2880277 := by exact prefixLift 2880277
  have htrace : WordTrace (prefixWord ++ tailWord_2880277) baseStart_2880277 baseEnd_2880277 := by
    simpa [prefixWord, tailWord_2880277, baseEnd_2880277] using wordTrace_append hprefix tailTrace_2880277
  have hstable : (prefixWord ++ tailWord_2880277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880277).length < 2 ^ (prefixWord ++ tailWord_2880277).sum := by decide
  have hdescent : baseEnd_2880277 < baseStart_2880277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880284 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2880284 : Nat := 118140960795 + 2880284 * 2 ^ 59
def prefixEnd_2880284 : Nat := 4983230072969 + 3 ^ 40 * 2880284 * 2
def baseEnd_2880284 : Nat := 492990037818238036434607

theorem tailTrace_2880284 : CollatzResearch.WordTrace tailWord_2880284 prefixEnd_2880284 492990037818238036434607 := by
  unfold tailWord_2880284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52526293948615228094543953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70035058598153637459391937 52526293948615228094543953)
  ·
    refine ⟨39394720461461421070907965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52526293948615228094543953 39394720461461421070907965)
    ·
      refine ⟨14773020173048032901590487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39394720461461421070907965 14773020173048032901590487)
      ·
        refine ⟨22159530259572049352385731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14773020173048032901590487 22159530259572049352385731)
        ·
          refine ⟨33239295389358074028578597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22159530259572049352385731 33239295389358074028578597)
          ·
            refine ⟨6232367885504638880358487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33239295389358074028578597 6232367885504638880358487)
            ·
              refine ⟨9348551828256958320537731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232367885504638880358487 9348551828256958320537731)
              ·
                refine ⟨14022827742385437480806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9348551828256958320537731 14022827742385437480806597)
                ·
                  refine ⟨2629280201697269527651237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14022827742385437480806597 2629280201697269527651237)
                  ·
                    refine ⟨492990037818238036434607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2629280201697269527651237 492990037818238036434607)
                    ·
                      rfl

theorem cell23_2880284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2880284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880284 prefixEnd_2880284 := by exact prefixLift 2880284
  have htrace : WordTrace (prefixWord ++ tailWord_2880284) baseStart_2880284 baseEnd_2880284 := by
    simpa [prefixWord, tailWord_2880284, baseEnd_2880284] using wordTrace_append hprefix tailTrace_2880284
  have hstable : (prefixWord ++ tailWord_2880284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880284).length < 2 ^ (prefixWord ++ tailWord_2880284).sum := by decide
  have hdescent : baseEnd_2880284 < baseStart_2880284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880308 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2880308 : Nat := 118140960795 + 2880308 * 2 ^ 59
def prefixEnd_2880308 : Nat := 4983230072969 + 3 ^ 40 * 2880308 * 2
def baseEnd_2880308 : Nat := 1478982436990422015403711

theorem tailTrace_2880308 : CollatzResearch.WordTrace tailWord_2880308 prefixEnd_2880308 1478982436990422015403711 := by
  unfold tailWord_2880308
  simp only [CollatzResearch.WordTrace]
  refine ⟨52526731624571754143980789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70035642166095672191974385 52526731624571754143980789)
  ·
    refine ⟨4924381089803601950998199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52526731624571754143980789 4924381089803601950998199)
    ·
      refine ⟨7386571634705402926497299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924381089803601950998199 7386571634705402926497299)
      ·
        refine ⟨11079857452058104389745949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386571634705402926497299 11079857452058104389745949)
        ·
          refine ⟨4154946544521789146154731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11079857452058104389745949 4154946544521789146154731)
          ·
            refine ⟨6232419816782683719232097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154946544521789146154731 6232419816782683719232097)
            ·
              refine ⟨4674314862587012789424073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232419816782683719232097 4674314862587012789424073)
              ·
                refine ⟨3505736146940259592068055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674314862587012789424073 3505736146940259592068055)
                ·
                  refine ⟨5258604220410389388102083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505736146940259592068055 5258604220410389388102083)
                  ·
                    refine ⟨7887906330615584082153125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5258604220410389388102083 7887906330615584082153125)
                    ·
                      refine ⟨1478982436990422015403711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7887906330615584082153125 1478982436990422015403711)
                      ·
                        rfl

theorem cell23_2880308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2880308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880308 prefixEnd_2880308 := by exact prefixLift 2880308
  have htrace : WordTrace (prefixWord ++ tailWord_2880308) baseStart_2880308 baseEnd_2880308 := by
    simpa [prefixWord, tailWord_2880308, baseEnd_2880308] using wordTrace_append hprefix tailTrace_2880308
  have hstable : (prefixWord ++ tailWord_2880308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880308).length < 2 ^ (prefixWord ++ tailWord_2880308).sum := by decide
  have hdescent : baseEnd_2880308 < baseStart_2880308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880341 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2880341 : Nat := 118140960795 + 2880341 * 2 ^ 59
def prefixEnd_2880341 : Nat := 4983230072969 + 3 ^ 40 * 2880341 * 2
def baseEnd_2880341 : Nat := 1478999381852020386291059

theorem tailTrace_2880341 : CollatzResearch.WordTrace tailWord_2880341 prefixEnd_2880341 1478999381852020386291059 := by
  unfold tailWord_2880341
  simp only [CollatzResearch.WordTrace]
  refine ⟨105054666858023954923912877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70036444572015969949275251 105054666858023954923912877)
  ·
    refine ⟨39395500071758983096467329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105054666858023954923912877 39395500071758983096467329)
    ·
      refine ⟨29546625053819237322350497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39395500071758983096467329 29546625053819237322350497)
      ·
        refine ⟨22159968790364427991762873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29546625053819237322350497 22159968790364427991762873)
        ·
          refine ⟨16619976592773320993822155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22159968790364427991762873 16619976592773320993822155)
          ·
            refine ⟨24929964889159981490733233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16619976592773320993822155 24929964889159981490733233)
            ·
              refine ⟨18697473666869986118049925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24929964889159981490733233 18697473666869986118049925)
              ·
                refine ⟨3505776312538122397134361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18697473666869986118049925 3505776312538122397134361)
                ·
                  refine ⟨2629332234403591797850771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505776312538122397134361 2629332234403591797850771)
                  ·
                    refine ⟨3943998351605387696776157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629332234403591797850771 3943998351605387696776157)
                    ·
                      refine ⟨1478999381852020386291059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3943998351605387696776157 1478999381852020386291059)
                      ·
                        rfl

theorem cell23_2880341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2880341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880341 prefixEnd_2880341 := by exact prefixLift 2880341
  have htrace : WordTrace (prefixWord ++ tailWord_2880341) baseStart_2880341 baseEnd_2880341 := by
    simpa [prefixWord, tailWord_2880341, baseEnd_2880341] using wordTrace_append hprefix tailTrace_2880341
  have hstable : (prefixWord ++ tailWord_2880341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880341).length < 2 ^ (prefixWord ++ tailWord_2880341).sum := by decide
  have hdescent : baseEnd_2880341 < baseStart_2880341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880357 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2880357 : Nat := 118140960795 + 2880357 * 2 ^ 59
def prefixEnd_2880357 : Nat := 4983230072969 + 3 ^ 40 * 2880357 * 2
def baseEnd_2880357 : Nat := 493002532514164107896995

theorem tailTrace_2880357 : CollatzResearch.WordTrace tailWord_2880357 prefixEnd_2880357 493002532514164107896995 := by
  unfold tailWord_2880357
  simp only [CollatzResearch.WordTrace]
  refine ⟨105055250425965989656495325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70036833617310659770996883 105055250425965989656495325)
  ·
    refine ⟨39395718909737246121185747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105055250425965989656495325 39395718909737246121185747)
    ·
      refine ⟨59093578364605869181778621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39395718909737246121185747 59093578364605869181778621)
      ·
        refine ⟨22160091886727200943166983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59093578364605869181778621 22160091886727200943166983)
        ·
          refine ⟨33240137830090801414750475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22160091886727200943166983 33240137830090801414750475)
          ·
            refine ⟨49860206745136202122125713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33240137830090801414750475 49860206745136202122125713)
            ·
              refine ⟨37395155058852151591594285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49860206745136202122125713 37395155058852151591594285)
              ·
                refine ⟨14023183147069556846847857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37395155058852151591594285 14023183147069556846847857)
                ·
                  refine ⟨10517387360302167635135893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14023183147069556846847857 10517387360302167635135893)
                  ·
                    refine ⟨493002532514164107896995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10517387360302167635135893 493002532514164107896995)
                    ·
                      rfl

theorem cell23_2880357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2880357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880357 prefixEnd_2880357 := by exact prefixLift 2880357
  have htrace : WordTrace (prefixWord ++ tailWord_2880357) baseStart_2880357 baseEnd_2880357 := by
    simpa [prefixWord, tailWord_2880357, baseEnd_2880357] using wordTrace_append hprefix tailTrace_2880357
  have hstable : (prefixWord ++ tailWord_2880357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880357).length < 2 ^ (prefixWord ++ tailWord_2880357).sum := by decide
  have hdescent : baseEnd_2880357 < baseStart_2880357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880381 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_2880381 : Nat := 118140960795 + 2880381 * 2 ^ 59
def prefixEnd_2880381 : Nat := 4983230072969 + 3 ^ 40 * 2880381 * 2
def baseEnd_2880381 : Nat := 1479019921078200229790875

theorem tailTrace_2880381 : CollatzResearch.WordTrace tailWord_2880381 prefixEnd_2880381 1479019921078200229790875 := by
  unfold tailWord_2880381
  simp only [CollatzResearch.WordTrace]
  refine ⟨105056125777879041755368997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70037417185252694503579331 105056125777879041755368997)
  ·
    refine ⟨19698023583352320329131687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105056125777879041755368997 19698023583352320329131687)
    ·
      refine ⟨29547035375028480493697531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19698023583352320329131687 29547035375028480493697531)
      ·
        refine ⟨44320553062542720740546297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29547035375028480493697531 44320553062542720740546297)
        ·
          refine ⟨33240414796907040555409723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44320553062542720740546297 33240414796907040555409723)
          ·
            refine ⟨49860622195360560833114585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33240414796907040555409723 49860622195360560833114585)
            ·
              refine ⟨37395466646520420624835939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49860622195360560833114585 37395466646520420624835939)
              ·
                refine ⟨56093199969780630937253909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37395466646520420624835939 56093199969780630937253909)
                ·
                  refine ⟨2629368748583467075183777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56093199969780630937253909 2629368748583467075183777)
                  ·
                    refine ⟨1972026561437600306387833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2629368748583467075183777 1972026561437600306387833)
                    ·
                      refine ⟨1479019921078200229790875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972026561437600306387833 1479019921078200229790875)
                      ·
                        rfl

theorem cell23_2880381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_2880381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880381 prefixEnd_2880381 := by exact prefixLift 2880381
  have htrace : WordTrace (prefixWord ++ tailWord_2880381) baseStart_2880381 baseEnd_2880381 := by
    simpa [prefixWord, tailWord_2880381, baseEnd_2880381] using wordTrace_append hprefix tailTrace_2880381
  have hstable : (prefixWord ++ tailWord_2880381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880381).length < 2 ^ (prefixWord ++ tailWord_2880381).sum := by decide
  have hdescent : baseEnd_2880381 < baseStart_2880381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880404 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2880404 : Nat := 118140960795 + 2880404 * 2 ^ 59
def prefixEnd_2880404 : Nat := 4983230072969 + 3 ^ 40 * 2880404 * 2
def baseEnd_2880404 : Nat := 164336859014805959978141

theorem tailTrace_2880404 : CollatzResearch.WordTrace tailWord_2880404 prefixEnd_2880404 164336859014805959978141 := by
  unfold tailWord_2880404
  simp only [CollatzResearch.WordTrace]
  refine ⟨52528482328397858341728133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70037976437863811122304177 52528482328397858341728133)
  ·
    refine ⟨9849090436574598439074025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52528482328397858341728133 9849090436574598439074025)
    ·
      refine ⟨7386817827430948829305519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9849090436574598439074025 7386817827430948829305519)
      ·
        refine ⟨11080226741146423243958279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386817827430948829305519 11080226741146423243958279)
        ·
          refine ⟨16620340111719634865937419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11080226741146423243958279 16620340111719634865937419)
          ·
            refine ⟨24930510167579452298906129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16620340111719634865937419 24930510167579452298906129)
            ·
              refine ⟨18697882625684589224179597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24930510167579452298906129 18697882625684589224179597)
              ·
                refine ⟨7011705984631720959067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18697882625684589224179597 7011705984631720959067349)
                ·
                  refine ⟨164336859014805959978141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7011705984631720959067349 164336859014805959978141)
                  ·
                    rfl

theorem cell23_2880404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2880404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880404 prefixEnd_2880404 := by exact prefixLift 2880404
  have htrace : WordTrace (prefixWord ++ tailWord_2880404) baseStart_2880404 baseEnd_2880404 := by
    simpa [prefixWord, tailWord_2880404, baseEnd_2880404] using wordTrace_append hprefix tailTrace_2880404
  have hstable : (prefixWord ++ tailWord_2880404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880404).length < 2 ^ (prefixWord ++ tailWord_2880404).sum := by decide
  have hdescent : baseEnd_2880404 < baseStart_2880404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880531 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 6, 3, 2]
def baseStart_2880531 : Nat := 118140960795 + 2880531 * 2 ^ 59
def prefixEnd_2880531 : Nat := 4983230072969 + 3 ^ 40 * 2880531 * 2
def baseEnd_2880531 : Nat := 1479096943176374642915185

theorem tailTrace_2880531 : CollatzResearch.WordTrace tailWord_2880531 prefixEnd_2880531 1479096943176374642915185 := by
  unfold tailWord_2880531
  simp only [CollatzResearch.WordTrace]
  refine ⟨105061596727335617373329447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70041064484890411582219631 105061596727335617373329447)
  ·
    refine ⟨157592395091003426059994171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105061596727335617373329447 157592395091003426059994171)
    ·
      refine ⟨236388592636505139089991257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157592395091003426059994171 236388592636505139089991257)
      ·
        refine ⟨177291444477378854317493443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236388592636505139089991257 177291444477378854317493443)
        ·
          refine ⟨265937166716068281476240165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177291444477378854317493443 265937166716068281476240165)
          ·
            refine ⟨49863218759262802776795031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265937166716068281476240165 49863218759262802776795031)
            ·
              refine ⟨74794828138894204165192547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49863218759262802776795031 74794828138894204165192547)
              ·
                refine ⟨112192242208341306247788821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74794828138894204165192547 112192242208341306247788821)
                ·
                  refine ⟨5259011353515998730365101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112192242208341306247788821 5259011353515998730365101)
                  ·
                    refine ⟨1972129257568499523886913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5259011353515998730365101 1972129257568499523886913)
                    ·
                      refine ⟨1479096943176374642915185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1972129257568499523886913 1479096943176374642915185)
                      ·
                        rfl

theorem cell23_2880531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3, 2].length) (baseStart_2880531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880531 prefixEnd_2880531 := by exact prefixLift 2880531
  have htrace : WordTrace (prefixWord ++ tailWord_2880531) baseStart_2880531 baseEnd_2880531 := by
    simpa [prefixWord, tailWord_2880531, baseEnd_2880531] using wordTrace_append hprefix tailTrace_2880531
  have hstable : (prefixWord ++ tailWord_2880531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880531).length < 2 ^ (prefixWord ++ tailWord_2880531).sum := by decide
  have hdescent : baseEnd_2880531 < baseStart_2880531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880572 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_2880572 : Nat := 118140960795 + 2880572 * 2 ^ 59
def prefixEnd_2880572 : Nat := 4983230072969 + 3 ^ 40 * 2880572 * 2
def baseEnd_2880572 : Nat := 1479117995883208982502497

theorem tailTrace_2880572 : CollatzResearch.WordTrace tailWord_2880572 prefixEnd_2880572 1479117995883208982502497 := by
  unfold tailWord_2880572
  simp only [CollatzResearch.WordTrace]
  refine ⟨52531546060093540687785985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70042061413458054250381313 52531546060093540687785985)
  ·
    refine ⟨39398659545070155515839489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52531546060093540687785985 39398659545070155515839489)
    ·
      refine ⟨29548994658802616636879617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39398659545070155515839489 29548994658802616636879617)
      ·
        refine ⟨22161745994101962477659713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29548994658802616636879617 22161745994101962477659713)
        ·
          refine ⟨16621309495576471858244785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22161745994101962477659713 16621309495576471858244785)
          ·
            refine ⟨12465982121682353893683589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16621309495576471858244785 12465982121682353893683589)
            ·
              refine ⟨2337371647815441355065673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12465982121682353893683589 2337371647815441355065673)
              ·
                refine ⟨1753028735861581016299255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337371647815441355065673 1753028735861581016299255)
                ·
                  refine ⟨2629543103792371524448883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753028735861581016299255 2629543103792371524448883)
                  ·
                    refine ⟨3944314655688557286673325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2629543103792371524448883 3944314655688557286673325)
                    ·
                      refine ⟨1479117995883208982502497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3944314655688557286673325 1479117995883208982502497)
                      ·
                        rfl

theorem cell23_2880572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_2880572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2880572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2880572 prefixEnd_2880572 := by exact prefixLift 2880572
  have htrace : WordTrace (prefixWord ++ tailWord_2880572) baseStart_2880572 baseEnd_2880572 := by
    simpa [prefixWord, tailWord_2880572, baseEnd_2880572] using wordTrace_append hprefix tailTrace_2880572
  have hstable : (prefixWord ++ tailWord_2880572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880572).length < 2 ^ (prefixWord ++ tailWord_2880572).sum := by decide
  have hdescent : baseEnd_2880572 < baseStart_2880572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
