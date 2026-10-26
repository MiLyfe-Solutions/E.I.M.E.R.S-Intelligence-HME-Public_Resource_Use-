import V185TrunkScan23Chunk0727

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4305892 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_4305892 : Nat := 118140960795 + 4305892 * 2 ^ 59
def prefixEnd_4305892 : Nat := 4983230072969 + 3 ^ 40 * 4305892 * 2
def baseEnd_4305892 : Nat := 2210992242349572411447569

theorem tailTrace_4305892 : CollatzResearch.WordTrace tailWord_4305892 prefixEnd_4305892 2210992242349572411447569 := by
  unfold tailWord_4305892
  simp only [CollatzResearch.WordTrace]
  refine ⟨78524391658248073325747965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104699188877664097767663953 78524391658248073325747965)
  ·
    refine ⟨29446646871843027497155487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78524391658248073325747965 29446646871843027497155487)
    ·
      refine ⟨44169970307764541245733231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29446646871843027497155487 44169970307764541245733231)
      ·
        refine ⟨66254955461646811868599847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44169970307764541245733231 66254955461646811868599847)
        ·
          refine ⟨99382433192470217802899771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66254955461646811868599847 99382433192470217802899771)
          ·
            refine ⟨149073649788705326704349657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99382433192470217802899771 149073649788705326704349657)
            ·
              refine ⟨111805237341528995028262243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149073649788705326704349657 111805237341528995028262243)
              ·
                refine ⟨167707856012293492542393365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111805237341528995028262243 167707856012293492542393365)
                ·
                  refine ⟨7861305750576257462924689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 167707856012293492542393365 7861305750576257462924689)
                  ·
                    refine ⟨5895979312932193097193517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7861305750576257462924689 5895979312932193097193517)
                    ·
                      refine ⟨2210992242349572411447569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5895979312932193097193517 2210992242349572411447569)
                      ·
                        rfl

theorem cell23_4305892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_4305892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305892 prefixEnd_4305892 := by exact prefixLift 4305892
  have htrace : WordTrace (prefixWord ++ tailWord_4305892) baseStart_4305892 baseEnd_4305892 := by
    simpa [prefixWord, tailWord_4305892, baseEnd_4305892] using wordTrace_append hprefix tailTrace_4305892
  have hstable : (prefixWord ++ tailWord_4305892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305892).length < 2 ^ (prefixWord ++ tailWord_4305892).sum := by decide
  have hdescent : baseEnd_4305892 < baseStart_4305892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305916 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_4305916 : Nat := 118140960795 + 4305916 * 2 ^ 59
def prefixEnd_4305916 : Nat := 4983230072969 + 3 ^ 40 * 4305916 * 2
def baseEnd_4305916 : Nat := 737001521961760105849153

theorem tailTrace_4305916 : CollatzResearch.WordTrace tailWord_4305916 prefixEnd_4305916 737001521961760105849153 := by
  unfold tailWord_4305916
  simp only [CollatzResearch.WordTrace]
  refine ⟨78524829334204599375184801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104699772445606132500246401 78524829334204599375184801)
  ·
    refine ⟨58893622000653449531388601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78524829334204599375184801 58893622000653449531388601)
    ·
      refine ⟨44170216500490087148541451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58893622000653449531388601 44170216500490087148541451)
      ·
        refine ⟨66255324750735130722812177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44170216500490087148541451 66255324750735130722812177)
        ·
          refine ⟨49691493563051348042109133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66255324750735130722812177 49691493563051348042109133)
          ·
            refine ⟨18634310086144255515790925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49691493563051348042109133 18634310086144255515790925)
            ·
              refine ⟨6987866282304095818421597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18634310086144255515790925 6987866282304095818421597)
              ·
                refine ⟨2620449855864035931908099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6987866282304095818421597 2620449855864035931908099)
                ·
                  refine ⟨3930674783796053897862149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620449855864035931908099 3930674783796053897862149)
                  ·
                    refine ⟨737001521961760105849153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930674783796053897862149 737001521961760105849153)
                    ·
                      rfl

theorem cell23_4305916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_4305916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305916 prefixEnd_4305916 := by exact prefixLift 4305916
  have htrace : WordTrace (prefixWord ++ tailWord_4305916) baseStart_4305916 baseEnd_4305916 := by
    simpa [prefixWord, tailWord_4305916, baseEnd_4305916] using wordTrace_append hprefix tailTrace_4305916
  have hstable : (prefixWord ++ tailWord_4305916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305916).length < 2 ^ (prefixWord ++ tailWord_4305916).sum := by decide
  have hdescent : baseEnd_4305916 < baseStart_4305916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305935 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_4305935 : Nat := 118140960795 + 4305935 * 2 ^ 59
def prefixEnd_4305935 : Nat := 4983230072969 + 3 ^ 40 * 4305935 * 2
def baseEnd_4305935 : Nat := 2211014322017715743209871

theorem tailTrace_4305935 : CollatzResearch.WordTrace tailWord_4305935 prefixEnd_4305935 2211014322017715743209871 := by
  unfold tailWord_4305935
  simp only [CollatzResearch.WordTrace]
  refine ⟨157050351655340364995311259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104700234436893576663540839 157050351655340364995311259)
  ·
    refine ⟨235575527483010547492966889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157050351655340364995311259 235575527483010547492966889)
    ·
      refine ⟨176681645612257910619725167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235575527483010547492966889 176681645612257910619725167)
      ·
        refine ⟨265022468418386865929587751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176681645612257910619725167 265022468418386865929587751)
        ·
          refine ⟨397533702627580298894381627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265022468418386865929587751 397533702627580298894381627)
          ·
            refine ⟨596300553941370448341572441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397533702627580298894381627 596300553941370448341572441)
            ·
              refine ⟨447225415456027836256179331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596300553941370448341572441 447225415456027836256179331)
              ·
                refine ⟨670838123184041754384268997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447225415456027836256179331 670838123184041754384268997)
                ·
                  refine ⟨125782148097007828947050437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670838123184041754384268997 125782148097007828947050437)
                  ·
                    refine ⟨23584152768188967927571957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125782148097007828947050437 23584152768188967927571957)
                    ·
                      refine ⟨2211014322017715743209871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23584152768188967927571957 2211014322017715743209871)
                      ·
                        rfl

theorem cell23_4305935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_4305935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305935 prefixEnd_4305935 := by exact prefixLift 4305935
  have htrace : WordTrace (prefixWord ++ tailWord_4305935) baseStart_4305935 baseEnd_4305935 := by
    simpa [prefixWord, tailWord_4305935, baseEnd_4305935] using wordTrace_append hprefix tailTrace_4305935
  have hstable : (prefixWord ++ tailWord_4305935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305935).length < 2 ^ (prefixWord ++ tailWord_4305935).sum := by decide
  have hdescent : baseEnd_4305935 < baseStart_4305935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305976 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 1, 5]
def baseStart_4305976 : Nat := 118140960795 + 4305976 * 2 ^ 59
def prefixEnd_4305976 : Nat := 4983230072969 + 3 ^ 40 * 4305976 * 2
def baseEnd_4305976 : Nat := 737011791574850027599061

theorem tailTrace_4305976 : CollatzResearch.WordTrace tailWord_4305976 prefixEnd_4305976 737011791574850027599061 := by
  unfold tailWord_4305976
  simp only [CollatzResearch.WordTrace]
  refine ⟨78525923524095914498776891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104701231365461219331702521 78525923524095914498776891)
  ·
    refine ⟨117788885286143871748165337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78525923524095914498776891 117788885286143871748165337)
    ·
      refine ⟨88341663964607903811124003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117788885286143871748165337 88341663964607903811124003)
      ·
        refine ⟨132512495946911855716686005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88341663964607903811124003 132512495946911855716686005)
        ·
          refine ⟨12423046495022986473439313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132512495946911855716686005 12423046495022986473439313)
          ·
            refine ⟨9317284871267239855079485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12423046495022986473439313 9317284871267239855079485)
            ·
              refine ⟨3493981826725214945654807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9317284871267239855079485 3493981826725214945654807)
              ·
                refine ⟨5240972740087822418482211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493981826725214945654807 5240972740087822418482211)
                ·
                  refine ⟨7861459110131733627723317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240972740087822418482211 7861459110131733627723317)
                  ·
                    refine ⟨737011791574850027599061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7861459110131733627723317 737011791574850027599061)
                    ·
                      rfl

theorem cell23_4305976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_4305976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305976 prefixEnd_4305976 := by exact prefixLift 4305976
  have htrace : WordTrace (prefixWord ++ tailWord_4305976) baseStart_4305976 baseEnd_4305976 := by
    simpa [prefixWord, tailWord_4305976, baseEnd_4305976] using wordTrace_append hprefix tailTrace_4305976
  have hstable : (prefixWord ++ tailWord_4305976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305976).length < 2 ^ (prefixWord ++ tailWord_4305976).sum := by decide
  have hdescent : baseEnd_4305976 < baseStart_4305976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305989 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_4305989 : Nat := 118140960795 + 4305989 * 2 ^ 59
def prefixEnd_4305989 : Nat := 4983230072969 + 3 ^ 40 * 4305989 * 2
def baseEnd_4305989 : Nat := 737014016657686177311541

theorem tailTrace_4305989 : CollatzResearch.WordTrace tailWord_4305989 prefixEnd_4305989 737014016657686177311541 := by
  unfold tailWord_4305989
  simp only [CollatzResearch.WordTrace]
  refine ⟨157052321197144732217777021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104701547464763154811851347 157052321197144732217777021)
  ·
    refine ⟨58894620448929274581666383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157052321197144732217777021 58894620448929274581666383)
    ·
      refine ⟨88341930673393911872499575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58894620448929274581666383 88341930673393911872499575)
      ·
        refine ⟨132512896010090867808749363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88341930673393911872499575 132512896010090867808749363)
        ·
          refine ⟨198769344015136301713124045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132512896010090867808749363 198769344015136301713124045)
          ·
            refine ⟨74538504005676113142421517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198769344015136301713124045 74538504005676113142421517)
            ·
              refine ⟨27951939002128542428408069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74538504005676113142421517 27951939002128542428408069)
              ·
                refine ⟨5240988562899101705326513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27951939002128542428408069 5240988562899101705326513)
                ·
                  refine ⟨3930741422174326278994885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240988562899101705326513 3930741422174326278994885)
                  ·
                    refine ⟨737014016657686177311541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930741422174326278994885 737014016657686177311541)
                    ·
                      rfl

theorem cell23_4305989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_4305989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305989 prefixEnd_4305989 := by exact prefixLift 4305989
  have htrace : WordTrace (prefixWord ++ tailWord_4305989) baseStart_4305989 baseEnd_4305989 := by
    simpa [prefixWord, tailWord_4305989, baseEnd_4305989] using wordTrace_append hprefix tailTrace_4305989
  have hstable : (prefixWord ++ tailWord_4305989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305989).length < 2 ^ (prefixWord ++ tailWord_4305989).sum := by decide
  have hdescent : baseEnd_4305989 < baseStart_4305989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305992 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_4305992 : Nat := 118140960795 + 4305992 * 2 ^ 59
def prefixEnd_4305992 : Nat := 4983230072969 + 3 ^ 40 * 4305992 * 2
def baseEnd_4305992 : Nat := 2211043590415022020197109

theorem tailTrace_4305992 : CollatzResearch.WordTrace tailWord_4305992 prefixEnd_4305992 2211043590415022020197109 := by
  unfold tailWord_4305992
  simp only [CollatzResearch.WordTrace]
  refine ⟨78526215308066931865068115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104701620410755909153424153 78526215308066931865068115)
  ·
    refine ⟨117789322962100397797602173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78526215308066931865068115 117789322962100397797602173)
    ·
      refine ⟨44170996110787649174100815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117789322962100397797602173 44170996110787649174100815)
      ·
        refine ⟨66256494166181473761151223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44170996110787649174100815 66256494166181473761151223)
        ·
          refine ⟨99384741249272210641726835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66256494166181473761151223 99384741249272210641726835)
          ·
            refine ⟨149077111873908315962590253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99384741249272210641726835 149077111873908315962590253)
            ·
              refine ⟨55903916952715618485971345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149077111873908315962590253 55903916952715618485971345)
              ·
                refine ⟨41927937714536713864478509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55903916952715618485971345 41927937714536713864478509)
                ·
                  refine ⟨15722976642951267699179441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41927937714536713864478509 15722976642951267699179441)
                  ·
                    refine ⟨11792232482213450774384581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15722976642951267699179441 11792232482213450774384581)
                    ·
                      refine ⟨2211043590415022020197109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11792232482213450774384581 2211043590415022020197109)
                      ·
                        rfl

theorem cell23_4305992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_4305992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305992 prefixEnd_4305992 := by exact prefixLift 4305992
  have htrace : WordTrace (prefixWord ++ tailWord_4305992) baseStart_4305992 baseEnd_4305992 := by
    simpa [prefixWord, tailWord_4305992, baseEnd_4305992] using wordTrace_append hprefix tailTrace_4305992
  have hstable : (prefixWord ++ tailWord_4305992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305992).length < 2 ^ (prefixWord ++ tailWord_4305992).sum := by decide
  have hdescent : baseEnd_4305992 < baseStart_4305992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305996 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4305996 : Nat := 118140960795 + 4305996 * 2 ^ 59
def prefixEnd_4305996 : Nat := 4983230072969 + 3 ^ 40 * 4305996 * 2
def baseEnd_4305996 : Nat := 2211045644337640004547091

theorem tailTrace_4305996 : CollatzResearch.WordTrace tailWord_4305996 prefixEnd_4305996 2211045644337640004547091 := by
  unfold tailWord_4305996
  simp only [CollatzResearch.WordTrace]
  refine ⟨78526288254059686206640921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104701717672079581608854561 78526288254059686206640921)
  ·
    refine ⟨58894716190544764654980691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78526288254059686206640921 58894716190544764654980691)
    ·
      refine ⟨88342074285817146982471037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58894716190544764654980691 88342074285817146982471037)
      ·
        refine ⟨33128277857181430118426639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88342074285817146982471037 33128277857181430118426639)
        ·
          refine ⟨49692416785772145177639959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33128277857181430118426639 49692416785772145177639959)
          ·
            refine ⟨74538625178658217766459939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49692416785772145177639959 74538625178658217766459939)
            ·
              refine ⟨111807937767987326649689909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74538625178658217766459939 111807937767987326649689909)
              ·
                refine ⟨10481994165748811873408429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111807937767987326649689909 10481994165748811873408429)
                ·
                  refine ⟨3930747812155804452528161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10481994165748811873408429 3930747812155804452528161)
                  ·
                    refine ⟨2948060859116853339396121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930747812155804452528161 2948060859116853339396121)
                    ·
                      refine ⟨2211045644337640004547091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948060859116853339396121 2211045644337640004547091)
                      ·
                        rfl

theorem cell23_4305996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4305996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305996 prefixEnd_4305996 := by exact prefixLift 4305996
  have htrace : WordTrace (prefixWord ++ tailWord_4305996) baseStart_4305996 baseEnd_4305996 := by
    simpa [prefixWord, tailWord_4305996, baseEnd_4305996] using wordTrace_append hprefix tailTrace_4305996
  have hstable : (prefixWord ++ tailWord_4305996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305996).length < 2 ^ (prefixWord ++ tailWord_4305996).sum := by decide
  have hdescent : baseEnd_4305996 < baseStart_4305996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306030 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_4306030 : Nat := 118140960795 + 4306030 * 2 ^ 59
def prefixEnd_4306030 : Nat := 4983230072969 + 3 ^ 40 * 4306030 * 2
def baseEnd_4306030 : Nat := 2211063102679892871521935

theorem tailTrace_4306030 : CollatzResearch.WordTrace tailWord_4306030 prefixEnd_4306030 2211063102679892871521935 := by
  unfold tailWord_4306030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19631727073749524527502443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104702544393330797480013029 19631727073749524527502443)
  ·
    refine ⟨29447590610624286791253665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19631727073749524527502443 29447590610624286791253665)
    ·
      refine ⟨22085692957968215093440249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29447590610624286791253665 22085692957968215093440249)
      ·
        refine ⟨16564269718476161320080187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22085692957968215093440249 16564269718476161320080187)
        ·
          refine ⟨24846404577714241980120281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16564269718476161320080187 24846404577714241980120281)
          ·
            refine ⟨18634803433285681485090211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24846404577714241980120281 18634803433285681485090211)
            ·
              refine ⟨27952205149928522227635317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18634803433285681485090211 27952205149928522227635317)
              ·
                refine ⟨2620519232805798958840811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27952205149928522227635317 2620519232805798958840811)
                ·
                  refine ⟨3930778849208698438261217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620519232805798958840811 3930778849208698438261217)
                  ·
                    refine ⟨2948084136906523828695913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930778849208698438261217 2948084136906523828695913)
                    ·
                      refine ⟨2211063102679892871521935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948084136906523828695913 2211063102679892871521935)
                      ·
                        rfl

theorem cell23_4306030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_4306030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306030 prefixEnd_4306030 := by exact prefixLift 4306030
  have htrace : WordTrace (prefixWord ++ tailWord_4306030) baseStart_4306030 baseEnd_4306030 := by
    simpa [prefixWord, tailWord_4306030, baseEnd_4306030] using wordTrace_append hprefix tailTrace_4306030
  have hstable : (prefixWord ++ tailWord_4306030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306030).length < 2 ^ (prefixWord ++ tailWord_4306030).sum := by decide
  have hdescent : baseEnd_4306030 < baseStart_4306030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306090 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4306090 : Nat := 118140960795 + 4306090 * 2 ^ 59
def prefixEnd_4306090 : Nat := 4983230072969 + 3 ^ 40 * 4306090 * 2
def baseEnd_4306090 : Nat := 2211093911519162636771659

theorem tailTrace_4306090 : CollatzResearch.WordTrace tailWord_4306090 prefixEnd_4306090 2211093911519162636771659 := by
  unfold tailWord_4306090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39264001242444706616800931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104704003313185884311469149 39264001242444706616800931)
  ·
    refine ⟨58896001863667059925201397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39264001242444706616800931 58896001863667059925201397)
    ·
      refine ⟨5521500174718786867987631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58896001863667059925201397 5521500174718786867987631)
      ·
        refine ⟨8282250262078180301981447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5521500174718786867987631 8282250262078180301981447)
        ·
          refine ⟨12423375393117270452972171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8282250262078180301981447 12423375393117270452972171)
          ·
            refine ⟨18635063089675905679458257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12423375393117270452972171 18635063089675905679458257)
            ·
              refine ⟨13976297317256929259593693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18635063089675905679458257 13976297317256929259593693)
              ·
                refine ⟨5241111493971348472347635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13976297317256929259593693 5241111493971348472347635)
                ·
                  refine ⟨7861667240957022708521453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5241111493971348472347635 7861667240957022708521453)
                  ·
                    refine ⟨2948125215358883515695545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7861667240957022708521453 2948125215358883515695545)
                    ·
                      refine ⟨2211093911519162636771659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948125215358883515695545 2211093911519162636771659)
                      ·
                        rfl

theorem cell23_4306090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4306090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306090 prefixEnd_4306090 := by exact prefixLift 4306090
  have htrace : WordTrace (prefixWord ++ tailWord_4306090) baseStart_4306090 baseEnd_4306090 := by
    simpa [prefixWord, tailWord_4306090, baseEnd_4306090] using wordTrace_append hprefix tailTrace_4306090
  have hstable : (prefixWord ++ tailWord_4306090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306090).length < 2 ^ (prefixWord ++ tailWord_4306090).sum := by decide
  have hdescent : baseEnd_4306090 < baseStart_4306090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306103 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 2, 2, 2]
def baseStart_4306103 : Nat := 118140960795 + 4306103 * 2 ^ 59
def prefixEnd_4306103 : Nat := 4983230072969 + 3 ^ 40 * 4306103 * 2
def baseEnd_4306103 : Nat := 2211100586767671085909099

theorem tailTrace_4306103 : CollatzResearch.WordTrace tailWord_4306103 prefixEnd_4306103 2211100586767671085909099 := by
  unfold tailWord_4306103
  simp only [CollatzResearch.WordTrace]
  refine ⟨157056479118731729687426963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104704319412487819791617975 157056479118731729687426963)
  ·
    refine ⟨235584718678097594531140445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157056479118731729687426963 235584718678097594531140445)
    ·
      refine ⟨88344269504286597949177667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235584718678097594531140445 88344269504286597949177667)
      ·
        refine ⟨132516404256429896923766501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88344269504286597949177667 132516404256429896923766501)
        ·
          refine ⟨24846825798080605673206219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132516404256429896923766501 24846825798080605673206219)
          ·
            refine ⟨37270238697120908509809329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24846825798080605673206219 37270238697120908509809329)
            ·
              refine ⟨27952679022840681382356997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37270238697120908509809329 27952679022840681382356997)
              ·
                refine ⟨5241127316782627759191937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27952679022840681382356997 5241127316782627759191937)
                ·
                  refine ⟨3930845487586970819393953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241127316782627759191937 3930845487586970819393953)
                  ·
                    refine ⟨2948134115690228114545465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930845487586970819393953 2948134115690228114545465)
                    ·
                      refine ⟨2211100586767671085909099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948134115690228114545465 2211100586767671085909099)
                      ·
                        rfl

theorem cell23_4306103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_4306103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306103 prefixEnd_4306103 := by exact prefixLift 4306103
  have htrace : WordTrace (prefixWord ++ tailWord_4306103) baseStart_4306103 baseEnd_4306103 := by
    simpa [prefixWord, tailWord_4306103, baseEnd_4306103] using wordTrace_append hprefix tailTrace_4306103
  have hstable : (prefixWord ++ tailWord_4306103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306103).length < 2 ^ (prefixWord ++ tailWord_4306103).sum := by decide
  have hdescent : baseEnd_4306103 < baseStart_4306103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306109 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 7]
def baseStart_4306109 : Nat := 118140960795 + 4306109 * 2 ^ 59
def prefixEnd_4306109 : Nat := 4983230072969 + 3 ^ 40 * 4306109 * 2
def baseEnd_4306109 : Nat := 245678185294622006937119

theorem tailTrace_4306109 : CollatzResearch.WordTrace tailWord_4306109 prefixEnd_4306109 245678185294622006937119 := by
  unfold tailWord_4306109
  simp only [CollatzResearch.WordTrace]
  refine ⟨157056697956709992712145381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104704465304473328474763587 157056697956709992712145381)
  ·
    refine ⟨29448130866883123633527259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157056697956709992712145381 29448130866883123633527259)
    ·
      refine ⟨44172196300324685450290889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29448130866883123633527259 44172196300324685450290889)
      ·
        refine ⟨33129147225243514087718167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44172196300324685450290889 33129147225243514087718167)
        ·
          refine ⟨49693720837865271131577251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33129147225243514087718167 49693720837865271131577251)
          ·
            refine ⟨74540581256797906697365877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49693720837865271131577251 74540581256797906697365877)
            ·
              refine ⟨6988179492824803752878051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74540581256797906697365877 6988179492824803752878051)
              ·
                refine ⟨10482269239237205629317077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6988179492824803752878051 10482269239237205629317077)
                ·
                  refine ⟨245678185294622006937119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10482269239237205629317077 245678185294622006937119)
                  ·
                    rfl

theorem cell23_4306109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_4306109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306109 prefixEnd_4306109 := by exact prefixLift 4306109
  have htrace : WordTrace (prefixWord ++ tailWord_4306109) baseStart_4306109 baseEnd_4306109 := by
    simpa [prefixWord, tailWord_4306109, baseEnd_4306109] using wordTrace_append hprefix tailTrace_4306109
  have hstable : (prefixWord ++ tailWord_4306109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306109).length < 2 ^ (prefixWord ++ tailWord_4306109).sum := by decide
  have hdescent : baseEnd_4306109 < baseStart_4306109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306119 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_4306119 : Nat := 118140960795 + 4306119 * 2 ^ 59
def prefixEnd_4306119 : Nat := 4983230072969 + 3 ^ 40 * 4306119 * 2
def baseEnd_4306119 : Nat := 2211108802458143023309025

theorem tailTrace_4306119 : CollatzResearch.WordTrace tailWord_4306119 prefixEnd_4306119 2211108802458143023309025 := by
  unfold tailWord_4306119
  simp only [CollatzResearch.WordTrace]
  refine ⟨157057062686673764420009411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104704708457782509613339607 157057062686673764420009411)
  ·
    refine ⟨235585594030010646630014117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157057062686673764420009411 235585594030010646630014117)
    ·
      refine ⟨44172298880626996243127647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235585594030010646630014117 44172298880626996243127647)
      ·
        refine ⟨66258448320940494364691471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44172298880626996243127647 66258448320940494364691471)
        ·
          refine ⟨99387672481410741547037207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66258448320940494364691471 99387672481410741547037207)
          ·
            refine ⟨149081508722116112320555811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99387672481410741547037207 149081508722116112320555811)
            ·
              refine ⟨223622263083174168480833717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149081508722116112320555811 223622263083174168480833717)
              ·
                refine ⟨20964587164047578295078161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223622263083174168480833717 20964587164047578295078161)
                ·
                  refine ⟨15723440373035683721308621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20964587164047578295078161 15723440373035683721308621)
                  ·
                    refine ⟨5896290139888381395490733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15723440373035683721308621 5896290139888381395490733)
                    ·
                      refine ⟨2211108802458143023309025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5896290139888381395490733 2211108802458143023309025)
                      ·
                        rfl

theorem cell23_4306119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_4306119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306119 prefixEnd_4306119 := by exact prefixLift 4306119
  have htrace : WordTrace (prefixWord ++ tailWord_4306119) baseStart_4306119 baseEnd_4306119 := by
    simpa [prefixWord, tailWord_4306119, baseEnd_4306119] using wordTrace_append hprefix tailTrace_4306119
  have hstable : (prefixWord ++ tailWord_4306119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306119).length < 2 ^ (prefixWord ++ tailWord_4306119).sum := by decide
  have hdescent : baseEnd_4306119 < baseStart_4306119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306120 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_4306120 : Nat := 118140960795 + 4306120 * 2 ^ 59
def prefixEnd_4306120 : Nat := 4983230072969 + 3 ^ 40 * 4306120 * 2
def baseEnd_4306120 : Nat := 2211109315938797519396521

theorem tailTrace_4306120 : CollatzResearch.WordTrace tailWord_4306120 prefixEnd_4306120 2211109315938797519396521 := by
  unfold tailWord_4306120
  simp only [CollatzResearch.WordTrace]
  refine ⟨78528549579835070795397907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104704732773113427727197209 78528549579835070795397907)
  ·
    refine ⟨117792824369752606193096861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78528549579835070795397907 117792824369752606193096861)
    ·
      refine ⟨44172309138657227322411323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117792824369752606193096861 44172309138657227322411323)
      ·
        refine ⟨66258463707985840983616985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44172309138657227322411323 66258463707985840983616985)
        ·
          refine ⟨49693847780989380737712739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66258463707985840983616985 49693847780989380737712739)
          ·
            refine ⟨74540771671484071106569109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49693847780989380737712739 74540771671484071106569109)
            ·
              refine ⟨3494098672100815833120427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74540771671484071106569109 3494098672100815833120427)
              ·
                refine ⟨5241148008151223749680641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494098672100815833120427 5241148008151223749680641)
                ·
                  refine ⟨3930861006113417812260481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241148008151223749680641 3930861006113417812260481)
                  ·
                    refine ⟨2948145754585063359195361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930861006113417812260481 2948145754585063359195361)
                    ·
                      refine ⟨2211109315938797519396521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948145754585063359195361 2211109315938797519396521)
                      ·
                        rfl

theorem cell23_4306120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_4306120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306120 prefixEnd_4306120 := by exact prefixLift 4306120
  have htrace : WordTrace (prefixWord ++ tailWord_4306120) baseStart_4306120 baseEnd_4306120 := by
    simpa [prefixWord, tailWord_4306120, baseEnd_4306120] using wordTrace_append hprefix tailTrace_4306120
  have hstable : (prefixWord ++ tailWord_4306120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306120).length < 2 ^ (prefixWord ++ tailWord_4306120).sum := by decide
  have hdescent : baseEnd_4306120 < baseStart_4306120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306199 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 8]
def baseStart_4306199 : Nat := 118140960795 + 4306199 * 2 ^ 59
def prefixEnd_4306199 : Nat := 4983230072969 + 3 ^ 40 * 4306199 * 2
def baseEnd_4306199 : Nat := 245683320101166967812073

theorem tailTrace_4306199 : CollatzResearch.WordTrace tailWord_4306199 prefixEnd_4306199 245683320101166967812073 := by
  unfold tailWord_4306199
  simp only [CollatzResearch.WordTrace]
  refine ⟨157059980526383938082921651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104706653684255958721947767 157059980526383938082921651)
  ·
    refine ⟨235589970789575907124382477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157059980526383938082921651 235589970789575907124382477)
    ·
      refine ⟨88346239046090965171643429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235589970789575907124382477 88346239046090965171643429)
      ·
        refine ⟨16564919821142055969683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88346239046090965171643429 16564919821142055969683143)
        ·
          refine ⟨24847379731713083954524715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16564919821142055969683143 24847379731713083954524715)
          ·
            refine ⟨37271069597569625931787073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24847379731713083954524715 37271069597569625931787073)
            ·
              refine ⟨27953302198177219448840305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37271069597569625931787073 27953302198177219448840305)
              ·
                refine ⟨20964976648632914586630229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27953302198177219448840305 20964976648632914586630229)
                ·
                  refine ⟨245683320101166967812073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20964976648632914586630229 245683320101166967812073)
                  ·
                    rfl

theorem cell23_4306199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 8].length) (baseStart_4306199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306199 prefixEnd_4306199 := by exact prefixLift 4306199
  have htrace : WordTrace (prefixWord ++ tailWord_4306199) baseStart_4306199 baseEnd_4306199 := by
    simpa [prefixWord, tailWord_4306199, baseEnd_4306199] using wordTrace_append hprefix tailTrace_4306199
  have hstable : (prefixWord ++ tailWord_4306199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306199).length < 2 ^ (prefixWord ++ tailWord_4306199).sum := by decide
  have hdescent : baseEnd_4306199 < baseStart_4306199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306216 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 8]
def baseStart_4306216 : Nat := 118140960795 + 4306216 * 2 ^ 59
def prefixEnd_4306216 : Nat := 4983230072969 + 3 ^ 40 * 4306216 * 2
def baseEnd_4306216 : Nat := 245684290009069904866231

theorem tailTrace_4306216 : CollatzResearch.WordTrace tailWord_4306216 prefixEnd_4306216 245684290009069904866231 := by
  unfold tailWord_4306216
  simp only [CollatzResearch.WordTrace]
  refine ⟨78530300283661174993145251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104707067044881566657527001 78530300283661174993145251)
  ·
    refine ⟨117795450425491762489717877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78530300283661174993145251 117795450425491762489717877)
    ·
      refine ⟨11043323477389852733411051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117795450425491762489717877 11043323477389852733411051)
      ·
        refine ⟨16564985216084779100116577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11043323477389852733411051 16564985216084779100116577)
        ·
          refine ⟨12423738912063584325087433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16564985216084779100116577 12423738912063584325087433)
          ·
            refine ⟨9317804184047688243815575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12423738912063584325087433 9317804184047688243815575)
            ·
              refine ⟨13976706276071532365723363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9317804184047688243815575 13976706276071532365723363)
              ·
                refine ⟨20965059414107298548585045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13976706276071532365723363 20965059414107298548585045)
                ·
                  refine ⟨245684290009069904866231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20965059414107298548585045 245684290009069904866231)
                  ·
                    rfl

theorem cell23_4306216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_4306216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306216 prefixEnd_4306216 := by exact prefixLift 4306216
  have htrace : WordTrace (prefixWord ++ tailWord_4306216) baseStart_4306216 baseEnd_4306216 := by
    simpa [prefixWord, tailWord_4306216, baseEnd_4306216] using wordTrace_append hprefix tailTrace_4306216
  have hstable : (prefixWord ++ tailWord_4306216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306216).length < 2 ^ (prefixWord ++ tailWord_4306216).sum := by decide
  have hdescent : baseEnd_4306216 < baseStart_4306216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306259 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 3, 6]
def baseStart_4306259 : Nat := 118140960795 + 4306259 * 2 ^ 59
def prefixEnd_4306259 : Nat := 4983230072969 + 3 ^ 40 * 4306259 * 2
def baseEnd_4306259 : Nat := 737060229916590825186127

theorem tailTrace_4306259 : CollatzResearch.WordTrace tailWord_4306259 prefixEnd_4306259 737060229916590825186127 := by
  unfold tailWord_4306259
  simp only [CollatzResearch.WordTrace]
  refine ⟨157062168906166568330105831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104708112604111045553403887 157062168906166568330105831)
  ·
    refine ⟨235593253359249852495158747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157062168906166568330105831 235593253359249852495158747)
    ·
      refine ⟨353389880038874778742738121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235593253359249852495158747 353389880038874778742738121)
      ·
        refine ⟨265042410029156084057053591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353389880038874778742738121 265042410029156084057053591)
        ·
          refine ⟨397563615043734126085580387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265042410029156084057053591 397563615043734126085580387)
          ·
            refine ⟨596345422565601189128370581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397563615043734126085580387 596345422565601189128370581)
            ·
              refine ⟨27953691682762555740392371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 596345422565601189128370581 27953691682762555740392371)
              ·
                refine ⟨41930537524143833610588557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27953691682762555740392371 41930537524143833610588557)
                ·
                  refine ⟨15723951571553937603970709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41930537524143833610588557 15723951571553937603970709)
                  ·
                    refine ⟨737060229916590825186127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15723951571553937603970709 737060229916590825186127)
                    ·
                      rfl

theorem cell23_4306259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_4306259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306259 prefixEnd_4306259 := by exact prefixLift 4306259
  have htrace : WordTrace (prefixWord ++ tailWord_4306259) baseStart_4306259 baseEnd_4306259 := by
    simpa [prefixWord, tailWord_4306259, baseEnd_4306259] using wordTrace_append hprefix tailTrace_4306259
  have hstable : (prefixWord ++ tailWord_4306259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306259).length < 2 ^ (prefixWord ++ tailWord_4306259).sum := by decide
  have hdescent : baseEnd_4306259 < baseStart_4306259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306277 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 1, 1, 3]
def baseStart_4306277 : Nat := 118140960795 + 4306277 * 2 ^ 59
def prefixEnd_4306277 : Nat := 4983230072969 + 3 ^ 40 * 4306277 * 2
def baseEnd_4306277 : Nat := 2211189932401553405133299

theorem tailTrace_4306277 : CollatzResearch.WordTrace tailWord_4306277 prefixEnd_4306277 2211189932401553405133299 := by
  unfold tailWord_4306277
  simp only [CollatzResearch.WordTrace]
  refine ⟨157062825420101357404261085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104708550280067571602840723 157062825420101357404261085)
  ·
    refine ⟨58898559532538009026597907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157062825420101357404261085 58898559532538009026597907)
    ·
      refine ⟨88347839298807013539896861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58898559532538009026597907 88347839298807013539896861)
      ·
        refine ⟨33130439737052630077461323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88347839298807013539896861 33130439737052630077461323)
        ·
          refine ⟨49695659605578945116191985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33130439737052630077461323 49695659605578945116191985)
          ·
            refine ⟨37271744704184208837143989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49695659605578945116191985 37271744704184208837143989)
            ·
              refine ⟨3494226066017269578482249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37271744704184208837143989 3494226066017269578482249)
              ·
                refine ⟨2620669549512952183861687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494226066017269578482249 2620669549512952183861687)
                ·
                  refine ⟨3931004324269428275792531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620669549512952183861687 3931004324269428275792531)
                  ·
                    refine ⟨5896506486404142413688797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931004324269428275792531 5896506486404142413688797)
                    ·
                      refine ⟨2211189932401553405133299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5896506486404142413688797 2211189932401553405133299)
                      ·
                        rfl

theorem cell23_4306277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_4306277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306277 prefixEnd_4306277 := by exact prefixLift 4306277
  have htrace : WordTrace (prefixWord ++ tailWord_4306277) baseStart_4306277 baseEnd_4306277 := by
    simpa [prefixWord, tailWord_4306277, baseEnd_4306277] using wordTrace_append hprefix tailTrace_4306277
  have hstable : (prefixWord ++ tailWord_4306277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306277).length < 2 ^ (prefixWord ++ tailWord_4306277).sum := by decide
  have hdescent : baseEnd_4306277 < baseStart_4306277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306289 : List Nat := [1, 2, 2, 2, 1, 2, 3, 10]
def baseStart_4306289 : Nat := 118140960795 + 4306289 * 2 ^ 59
def prefixEnd_4306289 : Nat := 4983230072969 + 3 ^ 40 * 4306289 * 2
def baseEnd_4306289 : Nat := 81896151635903976229009

theorem tailTrace_4306289 : CollatzResearch.WordTrace tailWord_4306289 prefixEnd_4306289 81896151635903976229009 := by
  unfold tailWord_4306289
  simp only [CollatzResearch.WordTrace]
  refine ⟨157063263096057883453697921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104708842064038588969131947 157063263096057883453697921)
  ·
    refine ⟨117797447322043412590273441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157063263096057883453697921 117797447322043412590273441)
    ·
      refine ⟨88348085491532559442705081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117797447322043412590273441 88348085491532559442705081)
      ·
        refine ⟨66261064118649419582028811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88348085491532559442705081 66261064118649419582028811)
        ·
          refine ⟨99391596177974129373043217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66261064118649419582028811 99391596177974129373043217)
          ·
            refine ⟨74543697133480597029782413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99391596177974129373043217 74543697133480597029782413)
            ·
              refine ⟨27953886425055223886168405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74543697133480597029782413 27953886425055223886168405)
              ·
                refine ⟨81896151635903976229009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27953886425055223886168405 81896151635903976229009)
                ·
                  rfl

theorem cell23_4306289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 10].length) (baseStart_4306289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306289 prefixEnd_4306289 := by exact prefixLift 4306289
  have htrace : WordTrace (prefixWord ++ tailWord_4306289) baseStart_4306289 baseEnd_4306289 := by
    simpa [prefixWord, tailWord_4306289, baseEnd_4306289] using wordTrace_append hprefix tailTrace_4306289
  have hstable : (prefixWord ++ tailWord_4306289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306289).length < 2 ^ (prefixWord ++ tailWord_4306289).sum := by decide
  have hdescent : baseEnd_4306289 < baseStart_4306289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306313 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_4306313 : Nat := 118140960795 + 4306313 * 2 ^ 59
def prefixEnd_4306313 : Nat := 4983230072969 + 3 ^ 40 * 4306313 * 2
def baseEnd_4306313 : Nat := 2211208417705115264283133

theorem tailTrace_4306313 : CollatzResearch.WordTrace tailWord_4306313 prefixEnd_4306313 2211208417705115264283133 := by
  unfold tailWord_4306313
  simp only [CollatzResearch.WordTrace]
  refine ⟨157064138447970935552571593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104709425631980623701714395 157064138447970935552571593)
  ·
    refine ⟨117798103835978201664428695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157064138447970935552571593 117798103835978201664428695)
    ·
      refine ⟨176697155753967302496643043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117798103835978201664428695 176697155753967302496643043)
      ·
        refine ⟨265045733630950953744964565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176697155753967302496643043 265045733630950953744964565)
        ·
          refine ⟨6212009381975412978397607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 265045733630950953744964565 6212009381975412978397607)
          ·
            refine ⟨9318014072963119467596411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212009381975412978397607 9318014072963119467596411)
            ·
              refine ⟨13977021109444679201394617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318014072963119467596411 13977021109444679201394617)
              ·
                refine ⟨10482765832083509401045963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13977021109444679201394617 10482765832083509401045963)
                ·
                  refine ⟨15724148748125264101568945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10482765832083509401045963 15724148748125264101568945)
                  ·
                    refine ⟨11793111561093948076176709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15724148748125264101568945 11793111561093948076176709)
                    ·
                      refine ⟨2211208417705115264283133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11793111561093948076176709 2211208417705115264283133)
                      ·
                        rfl

theorem cell23_4306313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_4306313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306313 prefixEnd_4306313 := by exact prefixLift 4306313
  have htrace : WordTrace (prefixWord ++ tailWord_4306313) baseStart_4306313 baseEnd_4306313 := by
    simpa [prefixWord, tailWord_4306313, baseEnd_4306313] using wordTrace_append hprefix tailTrace_4306313
  have hstable : (prefixWord ++ tailWord_4306313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306313).length < 2 ^ (prefixWord ++ tailWord_4306313).sum := by decide
  have hdescent : baseEnd_4306313 < baseStart_4306313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306366 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_4306366 : Nat := 118140960795 + 4306366 * 2 ^ 59
def prefixEnd_4306366 : Nat := 4983230072969 + 3 ^ 40 * 4306366 * 2
def baseEnd_4306366 : Nat := 737078544059934518973463

theorem tailTrace_4306366 : CollatzResearch.WordTrace tailWord_4306366 prefixEnd_4306366 737078544059934518973463 := by
  unfold tailWord_4306366
  simp only [CollatzResearch.WordTrace]
  refine ⟨19633258939597365700531369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104710714344519283736167301 19633258939597365700531369)
  ·
    refine ⟨14724944204698024275398527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19633258939597365700531369 14724944204698024275398527)
    ·
      refine ⟨22087416307047036413097791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14724944204698024275398527 22087416307047036413097791)
      ·
        refine ⟨33131124460570554619646687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22087416307047036413097791 33131124460570554619646687)
        ·
          refine ⟨49696686690855831929470031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33131124460570554619646687 49696686690855831929470031)
          ·
            refine ⟨74545030036283747894205047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49696686690855831929470031 74545030036283747894205047)
            ·
              refine ⟨111817545054425621841307571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74545030036283747894205047 111817545054425621841307571)
              ·
                refine ⟨167726317581638432761961357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111817545054425621841307571 167726317581638432761961357)
                ·
                  refine ⟨62897369093114412285735509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167726317581638432761961357 62897369093114412285735509)
                  ·
                    refine ⟨737078544059934518973463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62897369093114412285735509 737078544059934518973463)
                    ·
                      rfl

theorem cell23_4306366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_4306366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306366 prefixEnd_4306366 := by exact prefixLift 4306366
  have htrace : WordTrace (prefixWord ++ tailWord_4306366) baseStart_4306366 baseEnd_4306366 := by
    simpa [prefixWord, tailWord_4306366, baseEnd_4306366] using wordTrace_append hprefix tailTrace_4306366
  have hstable : (prefixWord ++ tailWord_4306366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306366).length < 2 ^ (prefixWord ++ tailWord_4306366).sum := by decide
  have hdescent : baseEnd_4306366 < baseStart_4306366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306376 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_4306376 : Nat := 118140960795 + 4306376 * 2 ^ 59
def prefixEnd_4306376 : Nat := 4983230072969 + 3 ^ 40 * 4306376 * 2
def baseEnd_4306376 : Nat := 2211240766986348517795343

theorem tailTrace_4306376 : CollatzResearch.WordTrace tailWord_4306376 prefixEnd_4306376 2211240766986348517795343 := by
  unfold tailWord_4306376
  simp only [CollatzResearch.WordTrace]
  refine ⟨78533218123371348656057491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104710957497828464874743321 78533218123371348656057491)
  ·
    refine ⟨117799827185057022984086237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78533218123371348656057491 117799827185057022984086237)
    ·
      refine ⟨44174935194396383619032339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117799827185057022984086237 44174935194396383619032339)
      ·
        refine ⟨66262402791594575428548509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44174935194396383619032339 66262402791594575428548509)
        ·
          refine ⟨24848401046847965785705691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66262402791594575428548509 24848401046847965785705691)
          ·
            refine ⟨37272601570271948678558537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24848401046847965785705691 37272601570271948678558537)
            ·
              refine ⟨27954451177703961508918903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37272601570271948678558537 27954451177703961508918903)
              ·
                refine ⟨41931676766555942263378355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27954451177703961508918903 41931676766555942263378355)
                ·
                  refine ⟨62897515149833913395067533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41931676766555942263378355 62897515149833913395067533)
                  ·
                    refine ⟨23586568181187717523150325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62897515149833913395067533 23586568181187717523150325)
                    ·
                      refine ⟨2211240766986348517795343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23586568181187717523150325 2211240766986348517795343)
                      ·
                        rfl

theorem cell23_4306376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_4306376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306376 prefixEnd_4306376 := by exact prefixLift 4306376
  have htrace : WordTrace (prefixWord ++ tailWord_4306376) baseStart_4306376 baseEnd_4306376 := by
    simpa [prefixWord, tailWord_4306376, baseEnd_4306376] using wordTrace_append hprefix tailTrace_4306376
  have hstable : (prefixWord ++ tailWord_4306376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306376).length < 2 ^ (prefixWord ++ tailWord_4306376).sum := by decide
  have hdescent : baseEnd_4306376 < baseStart_4306376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306403 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4306403 : Nat := 118140960795 + 4306403 * 2 ^ 59
def prefixEnd_4306403 : Nat := 4983230072969 + 3 ^ 40 * 4306403 * 2
def baseEnd_4306403 : Nat := 2211254630964019912157719

theorem tailTrace_4306403 : CollatzResearch.WordTrace tailWord_4306403 prefixEnd_4306403 2211254630964019912157719 := by
  unfold tailWord_4306403
  simp only [CollatzResearch.WordTrace]
  refine ⟨157067421017644880923347863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104711614011763253948898575 157067421017644880923347863)
  ·
    refine ⟨235601131526467321385021795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157067421017644880923347863 235601131526467321385021795)
    ·
      refine ⟨353401697289700982077532693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235601131526467321385021795 353401697289700982077532693)
      ·
        refine ⟨16565704560454733534884345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 353401697289700982077532693 16565704560454733534884345)
        ·
          refine ⟨12424278420341050151163259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16565704560454733534884345 12424278420341050151163259)
          ·
            refine ⟨18636417630511575226744889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12424278420341050151163259 18636417630511575226744889)
            ·
              refine ⟨13977313222883681420058667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18636417630511575226744889 13977313222883681420058667)
              ·
                refine ⟨20965969834325522130088001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13977313222883681420058667 20965969834325522130088001)
                ·
                  refine ⟨15724477375744141597566001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20965969834325522130088001 15724477375744141597566001)
                  ·
                    refine ⟨11793358031808106198174501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15724477375744141597566001 11793358031808106198174501)
                    ·
                      refine ⟨2211254630964019912157719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11793358031808106198174501 2211254630964019912157719)
                      ·
                        rfl

theorem cell23_4306403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4306403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306403 prefixEnd_4306403 := by exact prefixLift 4306403
  have htrace : WordTrace (prefixWord ++ tailWord_4306403) baseStart_4306403 baseEnd_4306403 := by
    simpa [prefixWord, tailWord_4306403, baseEnd_4306403] using wordTrace_append hprefix tailTrace_4306403
  have hstable : (prefixWord ++ tailWord_4306403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306403).length < 2 ^ (prefixWord ++ tailWord_4306403).sum := by decide
  have hdescent : baseEnd_4306403 < baseStart_4306403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306407 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4306407 : Nat := 118140960795 + 4306407 * 2 ^ 59
def prefixEnd_4306407 : Nat := 4983230072969 + 3 ^ 40 * 4306407 * 2
def baseEnd_4306407 : Nat := 2211256684886637896507701

theorem tailTrace_4306407 : CollatzResearch.WordTrace tailWord_4306407 prefixEnd_4306407 2211256684886637896507701 := by
  unfold tailWord_4306407
  simp only [CollatzResearch.WordTrace]
  refine ⟨157067566909630389606493475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104711711273086926404328983 157067566909630389606493475)
  ·
    refine ⟨235601350364445584409740213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157067566909630389606493475 235601350364445584409740213)
    ·
      refine ⟨22087626596666773538413145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235601350364445584409740213 22087626596666773538413145)
      ·
        refine ⟨16565719947500080153809859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22087626596666773538413145 16565719947500080153809859)
        ·
          refine ⟨24848579921250120230714789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16565719947500080153809859 24848579921250120230714789)
          ·
            refine ⟨4659108735234397543259023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24848579921250120230714789 4659108735234397543259023)
            ·
              refine ⟨6988663102851596314888535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659108735234397543259023 6988663102851596314888535)
              ·
                refine ⟨10482994654277394472332803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6988663102851596314888535 10482994654277394472332803)
                ·
                  refine ⟨15724491981416091708499205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10482994654277394472332803 15724491981416091708499205)
                  ·
                    refine ⟨2948342246515517195343601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15724491981416091708499205 2948342246515517195343601)
                    ·
                      refine ⟨2211256684886637896507701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948342246515517195343601 2211256684886637896507701)
                      ·
                        rfl

theorem cell23_4306407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4306407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306407 prefixEnd_4306407 := by exact prefixLift 4306407
  have htrace : WordTrace (prefixWord ++ tailWord_4306407) baseStart_4306407 baseEnd_4306407 := by
    simpa [prefixWord, tailWord_4306407, baseEnd_4306407] using wordTrace_append hprefix tailTrace_4306407
  have hstable : (prefixWord ++ tailWord_4306407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306407).length < 2 ^ (prefixWord ++ tailWord_4306407).sum := by decide
  have hdescent : baseEnd_4306407 < baseStart_4306407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306426 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_4306426 : Nat := 118140960795 + 4306426 * 2 ^ 59
def prefixEnd_4306426 : Nat := 4983230072969 + 3 ^ 40 * 4306426 * 2
def baseEnd_4306426 : Nat := 737088813673024440723371

theorem tailTrace_4306426 : CollatzResearch.WordTrace tailWord_4306426 prefixEnd_4306426 737088813673024440723371 := by
  unfold tailWord_4306426
  simp only [CollatzResearch.WordTrace]
  refine ⟨39267064974140388962858783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104712173264374370567623421 39267064974140388962858783)
  ·
    refine ⟨58900597461210583444288175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39267064974140388962858783 58900597461210583444288175)
    ·
      refine ⟨88350896191815875166432263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58900597461210583444288175 88350896191815875166432263)
      ·
        refine ⟨132526344287723812749648395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88350896191815875166432263 132526344287723812749648395)
        ·
          refine ⟨198789516431585719124472593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132526344287723812749648395 198789516431585719124472593)
          ·
            refine ⟨149092137323689289343354445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198789516431585719124472593 149092137323689289343354445)
            ·
              refine ⟨55909551496383483503757917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149092137323689289343354445 55909551496383483503757917)
              ·
                refine ⟨20966081811143806313909219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55909551496383483503757917 20966081811143806313909219)
                ·
                  refine ⟨31449122716715709470863829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20966081811143806313909219 31449122716715709470863829)
                  ·
                    refine ⟨737088813673024440723371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31449122716715709470863829 737088813673024440723371)
                    ·
                      rfl

theorem cell23_4306426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_4306426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306426 prefixEnd_4306426 := by exact prefixLift 4306426
  have htrace : WordTrace (prefixWord ++ tailWord_4306426) baseStart_4306426 baseEnd_4306426 := by
    simpa [prefixWord, tailWord_4306426, baseEnd_4306426] using wordTrace_append hprefix tailTrace_4306426
  have hstable : (prefixWord ++ tailWord_4306426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306426).length < 2 ^ (prefixWord ++ tailWord_4306426).sum := by decide
  have hdescent : baseEnd_4306426 < baseStart_4306426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306453 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4306453 : Nat := 118140960795 + 4306453 * 2 ^ 59
def prefixEnd_4306453 : Nat := 4983230072969 + 3 ^ 40 * 4306453 * 2
def baseEnd_4306453 : Nat := 2211280304996744716532489

theorem tailTrace_4306453 : CollatzResearch.WordTrace tailWord_4306453 prefixEnd_4306453 2211280304996744716532489 := by
  unfold tailWord_4306453
  simp only [CollatzResearch.WordTrace]
  refine ⟨157069244667463739462668013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104712829778309159641778675 157069244667463739462668013)
  ·
    refine ⟨58900966750298902298500505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157069244667463739462668013 58900966750298902298500505)
    ·
      refine ⟨44175725062724176723875379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58900966750298902298500505 44175725062724176723875379)
      ·
        refine ⟨66263587594086265085813069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44175725062724176723875379 66263587594086265085813069)
        ·
          refine ⟨24848845347782349407179901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66263587594086265085813069 24848845347782349407179901)
          ·
            refine ⟨9318317005418381027692463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24848845347782349407179901 9318317005418381027692463)
            ·
              refine ⟨13977475508127571541538695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318317005418381027692463 13977475508127571541538695)
              ·
                refine ⟨20966213262191357312308043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13977475508127571541538695 20966213262191357312308043)
                ·
                  refine ⟨31449319893287035968462065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20966213262191357312308043 31449319893287035968462065)
                  ·
                    refine ⟨23586989919965276976346549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31449319893287035968462065 23586989919965276976346549)
                    ·
                      refine ⟨2211280304996744716532489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23586989919965276976346549 2211280304996744716532489)
                      ·
                        rfl

theorem cell23_4306453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4306453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306453 prefixEnd_4306453 := by exact prefixLift 4306453
  have htrace : WordTrace (prefixWord ++ tailWord_4306453) baseStart_4306453 baseEnd_4306453 := by
    simpa [prefixWord, tailWord_4306453, baseEnd_4306453] using wordTrace_append hprefix tailTrace_4306453
  have hstable : (prefixWord ++ tailWord_4306453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306453).length < 2 ^ (prefixWord ++ tailWord_4306453).sum := by decide
  have hdescent : baseEnd_4306453 < baseStart_4306453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306476 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_4306476 : Nat := 118140960795 + 4306476 * 2 ^ 59
def prefixEnd_4306476 : Nat := 4983230072969 + 3 ^ 40 * 4306476 * 2
def baseEnd_4306476 : Nat := 2211292115051798126544883

theorem tailTrace_4306476 : CollatzResearch.WordTrace tailWord_4306476 prefixEnd_4306476 2211292115051798126544883 := by
  unfold tailWord_4306476
  simp only [CollatzResearch.WordTrace]
  refine ⟨78535041773190207195377641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104713389030920276260503521 78535041773190207195377641)
  ·
    refine ⟨58901281329892655396533231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78535041773190207195377641 58901281329892655396533231)
    ·
      refine ⟨88351921994838983094799847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58901281329892655396533231 88351921994838983094799847)
      ·
        refine ⟨132527882992258474642199771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88351921994838983094799847 132527882992258474642199771)
        ·
          refine ⟨198791824488387711963299657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132527882992258474642199771 198791824488387711963299657)
          ·
            refine ⟨149093868366290783972474743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198791824488387711963299657 149093868366290783972474743)
            ·
              refine ⟨223640802549436175958712115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149093868366290783972474743 223640802549436175958712115)
              ·
                refine ⟨335461203824154263938068173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223640802549436175958712115 335461203824154263938068173)
                ·
                  refine ⟨125797951434057848976775565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335461203824154263938068173 125797951434057848976775565)
                  ·
                    refine ⟨47174231787771693366290837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125797951434057848976775565 47174231787771693366290837)
                    ·
                      refine ⟨2211292115051798126544883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47174231787771693366290837 2211292115051798126544883)
                      ·
                        rfl

theorem cell23_4306476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_4306476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306476 prefixEnd_4306476 := by exact prefixLift 4306476
  have htrace : WordTrace (prefixWord ++ tailWord_4306476) baseStart_4306476 baseEnd_4306476 := by
    simpa [prefixWord, tailWord_4306476, baseEnd_4306476] using wordTrace_append hprefix tailTrace_4306476
  have hstable : (prefixWord ++ tailWord_4306476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306476).length < 2 ^ (prefixWord ++ tailWord_4306476).sum := by decide
  have hdescent : baseEnd_4306476 < baseStart_4306476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306564 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_4306564 : Nat := 118140960795 + 4306564 * 2 ^ 59
def prefixEnd_4306564 : Nat := 4983230072969 + 3 ^ 40 * 4306564 * 2
def baseEnd_4306564 : Nat := 2211337301349393782244479

theorem tailTrace_4306564 : CollatzResearch.WordTrace tailWord_4306564 prefixEnd_4306564 2211337301349393782244479 := by
  unfold tailWord_4306564
  simp only [CollatzResearch.WordTrace]
  refine ⟨78536646585030802709979373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104715528780041070279972497 78536646585030802709979373)
  ·
    refine ⟨29451242469386551016242265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78536646585030802709979373 29451242469386551016242265)
    ·
      refine ⟨22088431852039913262181699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29451242469386551016242265 22088431852039913262181699)
      ·
        refine ⟨33132647778059869893272549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22088431852039913262181699 33132647778059869893272549)
        ·
          refine ⟨6212371458386225604988603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33132647778059869893272549 6212371458386225604988603)
          ·
            refine ⟨9318557187579338407482905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212371458386225604988603 9318557187579338407482905)
            ·
              refine ⟨6988917890684503805612179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9318557187579338407482905 6988917890684503805612179)
              ·
                refine ⟨10483376836026755708418269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6988917890684503805612179 10483376836026755708418269)
                ·
                  refine ⟨3931266313510033390656851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10483376836026755708418269 3931266313510033390656851)
                  ·
                    refine ⟨5896899470265050085985277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931266313510033390656851 5896899470265050085985277)
                    ·
                      refine ⟨2211337301349393782244479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5896899470265050085985277 2211337301349393782244479)
                      ·
                        rfl

theorem cell23_4306564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_4306564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306564 prefixEnd_4306564 := by exact prefixLift 4306564
  have htrace : WordTrace (prefixWord ++ tailWord_4306564) baseStart_4306564 baseEnd_4306564 := by
    simpa [prefixWord, tailWord_4306564, baseEnd_4306564] using wordTrace_append hprefix tailTrace_4306564
  have hstable : (prefixWord ++ tailWord_4306564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306564).length < 2 ^ (prefixWord ++ tailWord_4306564).sum := by decide
  have hdescent : baseEnd_4306564 < baseStart_4306564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306614 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4306614 : Nat := 118140960795 + 4306614 * 2 ^ 59
def prefixEnd_4306614 : Nat := 4983230072969 + 3 ^ 40 * 4306614 * 2
def baseEnd_4306614 : Nat := 737120991794039528873083

theorem tailTrace_4306614 : CollatzResearch.WordTrace tailWord_4306614 prefixEnd_4306614 737120991794039528873083 := by
  unfold tailWord_4306614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817194801242528997454931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104716744546586975972852597 9817194801242528997454931)
  ·
    refine ⟨14725792201863793496182397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817194801242528997454931 14725792201863793496182397)
    ·
      refine ⟨5522172075698922561068399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14725792201863793496182397 5522172075698922561068399)
      ·
        refine ⟨8283258113548383841602599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522172075698922561068399 8283258113548383841602599)
        ·
          refine ⟨12424887170322575762403899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8283258113548383841602599 12424887170322575762403899)
          ·
            refine ⟨18637330755483863643605849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12424887170322575762403899 18637330755483863643605849)
            ·
              refine ⟨13977998066612897732704387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18637330755483863643605849 13977998066612897732704387)
              ·
                refine ⟨20966997099919346599056581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13977998066612897732704387 20966997099919346599056581)
                ·
                  refine ⟨3931311956234877487323109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20966997099919346599056581 3931311956234877487323109)
                  ·
                    refine ⟨737120991794039528873083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931311956234877487323109 737120991794039528873083)
                    ·
                      rfl

theorem cell23_4306614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4306614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306614 prefixEnd_4306614 := by exact prefixLift 4306614
  have htrace : WordTrace (prefixWord ++ tailWord_4306614) baseStart_4306614 baseEnd_4306614 := by
    simpa [prefixWord, tailWord_4306614, baseEnd_4306614] using wordTrace_append hprefix tailTrace_4306614
  have hstable : (prefixWord ++ tailWord_4306614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306614).length < 2 ^ (prefixWord ++ tailWord_4306614).sum := by decide
  have hdescent : baseEnd_4306614 < baseStart_4306614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306623 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 7]
def baseStart_4306623 : Nat := 118140960795 + 4306623 * 2 ^ 59
def prefixEnd_4306623 : Nat := 4983230072969 + 3 ^ 40 * 4306623 * 2
def baseEnd_4306623 : Nat := 737122532236003017135569

theorem tailTrace_4306623 : CollatzResearch.WordTrace tailWord_4306623 prefixEnd_4306623 737122532236003017135569 := by
  unfold tailWord_4306623
  simp only [CollatzResearch.WordTrace]
  refine ⟨157075445076847858496356523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104716963384565238997571015 157075445076847858496356523)
  ·
    refine ⟨235613167615271787744534785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157075445076847858496356523 235613167615271787744534785)
    ·
      refine ⟨176709875711453840808401089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235613167615271787744534785 176709875711453840808401089)
      ·
        refine ⟨132532406783590380606300817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176709875711453840808401089 132532406783590380606300817)
        ·
          refine ⟨99399305087692785454725613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132532406783590380606300817 99399305087692785454725613)
          ·
            refine ⟨37274739407884794545522105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99399305087692785454725613 37274739407884794545522105)
            ·
              refine ⟨27956054555913595909141579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37274739407884794545522105 27956054555913595909141579)
              ·
                refine ⟨41934081833870393863712369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27956054555913595909141579 41934081833870393863712369)
                ·
                  refine ⟨31450561375402795397784277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41934081833870393863712369 31450561375402795397784277)
                  ·
                    refine ⟨737122532236003017135569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31450561375402795397784277 737122532236003017135569)
                    ·
                      rfl

theorem cell23_4306623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_4306623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306623 prefixEnd_4306623 := by exact prefixLift 4306623
  have htrace : WordTrace (prefixWord ++ tailWord_4306623) baseStart_4306623 baseEnd_4306623 := by
    simpa [prefixWord, tailWord_4306623, baseEnd_4306623] using wordTrace_append hprefix tailTrace_4306623
  have hstable : (prefixWord ++ tailWord_4306623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306623).length < 2 ^ (prefixWord ++ tailWord_4306623).sum := by decide
  have hdescent : baseEnd_4306623 < baseStart_4306623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306647 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 3, 3, 2]
def baseStart_4306647 : Nat := 118140960795 + 4306647 * 2 ^ 59
def prefixEnd_4306647 : Nat := 4983230072969 + 3 ^ 40 * 4306647 * 2
def baseEnd_4306647 : Nat := 2211379920243716957506597

theorem tailTrace_4306647 : CollatzResearch.WordTrace tailWord_4306647 prefixEnd_4306647 2211379920243716957506597 := by
  unfold tailWord_4306647
  simp only [CollatzResearch.WordTrace]
  refine ⟨157076320428760910595230195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104717546952507273730153463 157076320428760910595230195)
  ·
    refine ⟨235614480643141365892845293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157076320428760910595230195 235614480643141365892845293)
    ·
      refine ⟨88355430241178012209816985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235614480643141365892845293 88355430241178012209816985)
      ·
        refine ⟨66266572680883509157362739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88355430241178012209816985 66266572680883509157362739)
        ·
          refine ⟨99399859021325263736044109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66266572680883509157362739 99399859021325263736044109)
          ·
            refine ⟨37274947132996973901016541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99399859021325263736044109 37274947132996973901016541)
            ·
              refine ⟨13978105174873865212881203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37274947132996973901016541 13978105174873865212881203)
              ·
                refine ⟨20967157762310797819321805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13978105174873865212881203 20967157762310797819321805)
                ·
                  refine ⟨7862684160866549182245677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20967157762310797819321805 7862684160866549182245677)
                  ·
                    refine ⟨2948506560324955943342129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7862684160866549182245677 2948506560324955943342129)
                    ·
                      refine ⟨2211379920243716957506597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948506560324955943342129 2211379920243716957506597)
                      ·
                        rfl

theorem cell23_4306647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_4306647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306647 prefixEnd_4306647 := by exact prefixLift 4306647
  have htrace : WordTrace (prefixWord ++ tailWord_4306647) baseStart_4306647 baseEnd_4306647 := by
    simpa [prefixWord, tailWord_4306647, baseEnd_4306647] using wordTrace_append hprefix tailTrace_4306647
  have hstable : (prefixWord ++ tailWord_4306647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306647).length < 2 ^ (prefixWord ++ tailWord_4306647).sum := by decide
  have hdescent : baseEnd_4306647 < baseStart_4306647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306670 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4306670 : Nat := 118140960795 + 4306670 * 2 ^ 59
def prefixEnd_4306670 : Nat := 4983230072969 + 3 ^ 40 * 4306670 * 2
def baseEnd_4306670 : Nat := 737130576766256789172997

theorem tailTrace_4306670 : CollatzResearch.WordTrace tailWord_4306670 prefixEnd_4306670 737130576766256789172997 := by
  unfold tailWord_4306670
  simp only [CollatzResearch.WordTrace]
  refine ⟨19634644913459698190414683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104718106205118390348878309 19634644913459698190414683)
  ·
    refine ⟨29451967370189547285622025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19634644913459698190414683 29451967370189547285622025)
    ·
      refine ⟨22088975527642160464216519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29451967370189547285622025 22088975527642160464216519)
      ·
        refine ⟨33133463291463240696324779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22088975527642160464216519 33133463291463240696324779)
        ·
          refine ⟨49700194937194861044487169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33133463291463240696324779 49700194937194861044487169)
          ·
            refine ⟨37275146202896145783365377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49700194937194861044487169 37275146202896145783365377)
            ·
              refine ⟨27956359652172109337524033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37275146202896145783365377 27956359652172109337524033)
              ·
                refine ⟨20967269739129082003143025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27956359652172109337524033 20967269739129082003143025)
                ·
                  refine ⟨15725452304346811502357269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20967269739129082003143025 15725452304346811502357269)
                  ·
                    refine ⟨737130576766256789172997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15725452304346811502357269 737130576766256789172997)
                    ·
                      rfl

theorem cell23_4306670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4306670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306670 prefixEnd_4306670 := by exact prefixLift 4306670
  have htrace : WordTrace (prefixWord ++ tailWord_4306670) baseStart_4306670 baseEnd_4306670 := by
    simpa [prefixWord, tailWord_4306670, baseEnd_4306670] using wordTrace_append hprefix tailTrace_4306670
  have hstable : (prefixWord ++ tailWord_4306670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306670).length < 2 ^ (prefixWord ++ tailWord_4306670).sum := by decide
  have hdescent : baseEnd_4306670 < baseStart_4306670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306728 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_4306728 : Nat := 118140960795 + 4306728 * 2 ^ 59
def prefixEnd_4306728 : Nat := 4983230072969 + 3 ^ 40 * 4306728 * 2
def baseEnd_4306728 : Nat := 2211421512176731140593725

theorem tailTrace_4306728 : CollatzResearch.WordTrace tailWord_4306728 prefixEnd_4306728 2211421512176731140593725 := by
  unfold tailWord_4306728
  simp only [CollatzResearch.WordTrace]
  refine ⟨78539637370733730714464419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104719516494311640952619225 78539637370733730714464419)
  ·
    refine ⟨117809456056100596071696629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78539637370733730714464419 117809456056100596071696629)
    ·
      refine ⟨11044636505259430881721559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117809456056100596071696629 11044636505259430881721559)
      ·
        refine ⟨16566954757889146322582339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11044636505259430881721559 16566954757889146322582339)
        ·
          refine ⟨24850432136833719483873509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16566954757889146322582339 24850432136833719483873509)
          ·
            refine ⟨4659456025656322403226283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24850432136833719483873509 4659456025656322403226283)
            ·
              refine ⟨6989184038484483604839425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659456025656322403226283 6989184038484483604839425)
              ·
                refine ⟨5241888028863362703629569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6989184038484483604839425 5241888028863362703629569)
                ·
                  refine ⟨3931416021647522027722177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241888028863362703629569 3931416021647522027722177)
                  ·
                    refine ⟨2948562016235641520791633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3931416021647522027722177 2948562016235641520791633)
                    ·
                      refine ⟨2211421512176731140593725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948562016235641520791633 2211421512176731140593725)
                      ·
                        rfl

theorem cell23_4306728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_4306728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306728 prefixEnd_4306728 := by exact prefixLift 4306728
  have htrace : WordTrace (prefixWord ++ tailWord_4306728) baseStart_4306728 baseEnd_4306728 := by
    simpa [prefixWord, tailWord_4306728, baseEnd_4306728] using wordTrace_append hprefix tailTrace_4306728
  have hstable : (prefixWord ++ tailWord_4306728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306728).length < 2 ^ (prefixWord ++ tailWord_4306728).sum := by decide
  have hdescent : baseEnd_4306728 < baseStart_4306728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306734 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_4306734 : Nat := 118140960795 + 4306734 * 2 ^ 59
def prefixEnd_4306734 : Nat := 4983230072969 + 3 ^ 40 * 4306734 * 2
def baseEnd_4306734 : Nat := 245713843673406457457633

theorem tailTrace_4306734 : CollatzResearch.WordTrace tailWord_4306734 prefixEnd_4306734 245713843673406457457633 := by
  unfold tailWord_4306734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19634936697430715556705907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104719662386297149635764837 19634936697430715556705907)
  ·
    refine ⟨29452405046146073335058861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19634936697430715556705907 29452405046146073335058861)
    ·
      refine ⟨11044651892304777500647073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29452405046146073335058861 11044651892304777500647073)
      ·
        refine ⟨8283488919228583125485305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11044651892304777500647073 8283488919228583125485305)
        ·
          refine ⟨6212616689421437344113979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8283488919228583125485305 6212616689421437344113979)
          ·
            refine ⟨9318925034132156016170969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212616689421437344113979 9318925034132156016170969)
            ·
              refine ⟨6989193775599117012128227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9318925034132156016170969 6989193775599117012128227)
              ·
                refine ⟨10483790663398675518192341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989193775599117012128227 10483790663398675518192341)
                ·
                  refine ⟨245713843673406457457633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10483790663398675518192341 245713843673406457457633)
                  ·
                    rfl

theorem cell23_4306734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_4306734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306734 prefixEnd_4306734 := by exact prefixLift 4306734
  have htrace : WordTrace (prefixWord ++ tailWord_4306734) baseStart_4306734 baseEnd_4306734 := by
    simpa [prefixWord, tailWord_4306734, baseEnd_4306734] using wordTrace_append hprefix tailTrace_4306734
  have hstable : (prefixWord ++ tailWord_4306734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306734).length < 2 ^ (prefixWord ++ tailWord_4306734).sum := by decide
  have hdescent : baseEnd_4306734 < baseStart_4306734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306745 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4306745 : Nat := 118140960795 + 4306745 * 2 ^ 59
def prefixEnd_4306745 : Nat := 4983230072969 + 3 ^ 40 * 4306745 * 2
def baseEnd_4306745 : Nat := 2211430241347857574081147

theorem tailTrace_4306745 : CollatzResearch.WordTrace tailWord_4306745 prefixEnd_4306745 2211430241347857574081147 := by
  unfold tailWord_4306745
  simp only [CollatzResearch.WordTrace]
  refine ⟨157079894782405873332297689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104719929854937248888198459 157079894782405873332297689)
  ·
    refine ⟨117809921086804404999223267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157079894782405873332297689 117809921086804404999223267)
    ·
      refine ⟨176714881630206607498834901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117809921086804404999223267 176714881630206607498834901)
      ·
        refine ⟨4141755038207967363253943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 176714881630206607498834901 4141755038207967363253943)
        ·
          refine ⟨6212632557311951044880915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141755038207967363253943 6212632557311951044880915)
          ·
            refine ⟨9318948835967926567321373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212632557311951044880915 9318948835967926567321373)
            ·
              refine ⟨3494605813487972462745515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9318948835967926567321373 3494605813487972462745515)
              ·
                refine ⟨5241908720231958694118273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494605813487972462745515 5241908720231958694118273)
                ·
                  refine ⟨3931431540173969020588705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5241908720231958694118273 3931431540173969020588705)
                  ·
                    refine ⟨2948573655130476765441529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3931431540173969020588705 2948573655130476765441529)
                    ·
                      refine ⟨2211430241347857574081147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948573655130476765441529 2211430241347857574081147)
                      ·
                        rfl

theorem cell23_4306745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4306745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306745 prefixEnd_4306745 := by exact prefixLift 4306745
  have htrace : WordTrace (prefixWord ++ tailWord_4306745) baseStart_4306745 baseEnd_4306745 := by
    simpa [prefixWord, tailWord_4306745, baseEnd_4306745] using wordTrace_append hprefix tailTrace_4306745
  have hstable : (prefixWord ++ tailWord_4306745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306745).length < 2 ^ (prefixWord ++ tailWord_4306745).sum := by decide
  have hdescent : baseEnd_4306745 < baseStart_4306745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306810 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_4306810 : Nat := 118140960795 + 4306810 * 2 ^ 59
def prefixEnd_4306810 : Nat := 4983230072969 + 3 ^ 40 * 4306810 * 2
def baseEnd_4306810 : Nat := 2211463617590399819768347

theorem tailTrace_4306810 : CollatzResearch.WordTrace tailWord_4306810 prefixEnd_4306810 2211463617590399819768347 := by
  unfold tailWord_4306810
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270566381792597358353471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104721510351446926288942589 39270566381792597358353471)
  ·
    refine ⟨58905849572688896037530207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39270566381792597358353471 58905849572688896037530207)
    ·
      refine ⟨88358774359033344056295311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58905849572688896037530207 88358774359033344056295311)
      ·
        refine ⟨132538161538550016084442967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88358774359033344056295311 132538161538550016084442967)
        ·
          refine ⟨198807242307825024126664451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132538161538550016084442967 198807242307825024126664451)
          ·
            refine ⟨298210863461737536189996677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198807242307825024126664451 298210863461737536189996677)
            ·
              refine ⟨55914536899075788035624377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298210863461737536189996677 55914536899075788035624377)
              ·
                refine ⟨41935902674306841026718283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55914536899075788035624377 41935902674306841026718283)
                ·
                  refine ⟨62903854011460261540077425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41935902674306841026718283 62903854011460261540077425)
                  ·
                    refine ⟨47177890508595196155058069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62903854011460261540077425 47177890508595196155058069)
                    ·
                      refine ⟨2211463617590399819768347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47177890508595196155058069 2211463617590399819768347)
                      ·
                        rfl

theorem cell23_4306810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_4306810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306810 prefixEnd_4306810 := by exact prefixLift 4306810
  have htrace : WordTrace (prefixWord ++ tailWord_4306810) baseStart_4306810 baseEnd_4306810 := by
    simpa [prefixWord, tailWord_4306810, baseEnd_4306810] using wordTrace_append hprefix tailTrace_4306810
  have hstable : (prefixWord ++ tailWord_4306810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306810).length < 2 ^ (prefixWord ++ tailWord_4306810).sum := by decide
  have hdescent : baseEnd_4306810 < baseStart_4306810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306867 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 1, 6]
def baseStart_4306867 : Nat := 118140960795 + 4306867 * 2 ^ 59
def prefixEnd_4306867 : Nat := 4983230072969 + 3 ^ 40 * 4306867 * 2
def baseEnd_4306867 : Nat := 737164295329235365585195

theorem tailTrace_4306867 : CollatzResearch.WordTrace tailWord_4306867 prefixEnd_4306867 737164295329235365585195 := by
  unfold tailWord_4306867
  simp only [CollatzResearch.WordTrace]
  refine ⟨157084344487963888168238855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104722896325309258778825903 157084344487963888168238855)
  ·
    refine ⟨235626516731945832252358283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157084344487963888168238855 235626516731945832252358283)
    ·
      refine ⟨353439775097918748378537425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235626516731945832252358283 353439775097918748378537425)
      ·
        refine ⟨265079831323439061283903069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353439775097918748378537425 265079831323439061283903069)
        ·
          refine ⟨99404936746289647981463651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265079831323439061283903069 99404936746289647981463651)
          ·
            refine ⟨149107405119434471972195477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99404936746289647981463651 149107405119434471972195477)
            ·
              refine ⟨6989409614973490873696663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149107405119434471972195477 6989409614973490873696663)
              ·
                refine ⟨10484114422460236310544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989409614973490873696663 10484114422460236310544995)
                ·
                  refine ⟨15726171633690354465817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10484114422460236310544995 15726171633690354465817493)
                  ·
                    refine ⟨737164295329235365585195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15726171633690354465817493 737164295329235365585195)
                    ·
                      rfl

theorem cell23_4306867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 6].length) (baseStart_4306867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306867 prefixEnd_4306867 := by exact prefixLift 4306867
  have htrace : WordTrace (prefixWord ++ tailWord_4306867) baseStart_4306867 baseEnd_4306867 := by
    simpa [prefixWord, tailWord_4306867, baseEnd_4306867] using wordTrace_append hprefix tailTrace_4306867
  have hstable : (prefixWord ++ tailWord_4306867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306867).length < 2 ^ (prefixWord ++ tailWord_4306867).sum := by decide
  have hdescent : baseEnd_4306867 < baseStart_4306867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306878 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_4306878 : Nat := 118140960795 + 4306878 * 2 ^ 59
def prefixEnd_4306878 : Nat := 4983230072969 + 3 ^ 40 * 4306878 * 2
def baseEnd_4306878 : Nat := 2211498534274905553718035

theorem tailTrace_4306878 : CollatzResearch.WordTrace tailWord_4306878 prefixEnd_4306878 2211498534274905553718035 := by
  unfold tailWord_4306878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19635593211365504630861161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104723163793949358031259525 19635593211365504630861161)
  ·
    refine ⟨14726694908524128473145871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19635593211365504630861161 14726694908524128473145871)
    ·
      refine ⟨22090042362786192709718807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726694908524128473145871 22090042362786192709718807)
      ·
        refine ⟨33135063544179289064578211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22090042362786192709718807 33135063544179289064578211)
        ·
          refine ⟨49702595316268933596867317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33135063544179289064578211 49702595316268933596867317)
          ·
            refine ⟨4659618310900212524706311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49702595316268933596867317 4659618310900212524706311)
            ·
              refine ⟨6989427466350318787059467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659618310900212524706311 6989427466350318787059467)
              ·
                refine ⟨10484141199525478180589201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989427466350318787059467 10484141199525478180589201)
                ·
                  refine ⟨7863105899644108635441901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10484141199525478180589201 7863105899644108635441901)
                  ·
                    refine ⟨2948664712366540738290713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7863105899644108635441901 2948664712366540738290713)
                    ·
                      refine ⟨2211498534274905553718035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948664712366540738290713 2211498534274905553718035)
                      ·
                        rfl

theorem cell23_4306878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_4306878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306878 prefixEnd_4306878 := by exact prefixLift 4306878
  have htrace : WordTrace (prefixWord ++ tailWord_4306878) baseStart_4306878 baseEnd_4306878 := by
    simpa [prefixWord, tailWord_4306878, baseEnd_4306878] using wordTrace_append hprefix tailTrace_4306878
  have hstable : (prefixWord ++ tailWord_4306878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306878).length < 2 ^ (prefixWord ++ tailWord_4306878).sum := by decide
  have hdescent : baseEnd_4306878 < baseStart_4306878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306901 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_4306901 : Nat := 118140960795 + 4306901 * 2 ^ 59
def prefixEnd_4306901 : Nat := 4983230072969 + 3 ^ 40 * 4306901 * 2
def baseEnd_4306901 : Nat := 737170114776652987910143

theorem tailTrace_4306901 : CollatzResearch.WordTrace tailWord_4306901 prefixEnd_4306901 737170114776652987910143 := by
  unfold tailWord_4306901
  simp only [CollatzResearch.WordTrace]
  refine ⟨157085584569840711974976557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104723723046560474649984371 157085584569840711974976557)
  ·
    refine ⟨58907094213690266990616209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157085584569840711974976557 58907094213690266990616209)
    ·
      refine ⟨44180320660267700242962157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58907094213690266990616209 44180320660267700242962157)
      ·
        refine ⟨16567620247600387591110809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44180320660267700242962157 16567620247600387591110809)
        ·
          refine ⟨12425715185700290693333107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16567620247600387591110809 12425715185700290693333107)
          ·
            refine ⟨18638572778550436039999661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12425715185700290693333107 18638572778550436039999661)
            ·
              refine ⟨6989464791956413514999873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18638572778550436039999661 6989464791956413514999873)
              ·
                refine ⟨5242098593967310136249905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6989464791956413514999873 5242098593967310136249905)
                ·
                  refine ⟨3931573945475482602187429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5242098593967310136249905 3931573945475482602187429)
                  ·
                    refine ⟨737170114776652987910143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931573945475482602187429 737170114776652987910143)
                    ·
                      rfl

theorem cell23_4306901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_4306901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306901 prefixEnd_4306901 := by exact prefixLift 4306901
  have htrace : WordTrace (prefixWord ++ tailWord_4306901) baseStart_4306901 baseEnd_4306901 := by
    simpa [prefixWord, tailWord_4306901, baseEnd_4306901] using wordTrace_append hprefix tailTrace_4306901
  have hstable : (prefixWord ++ tailWord_4306901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306901).length < 2 ^ (prefixWord ++ tailWord_4306901).sum := by decide
  have hdescent : baseEnd_4306901 < baseStart_4306901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306937 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_4306937 : Nat := 118140960795 + 4306937 * 2 ^ 59
def prefixEnd_4306937 : Nat := 4983230072969 + 3 ^ 40 * 4306937 * 2
def baseEnd_4306937 : Nat := 2211528829633520822880263

theorem tailTrace_4306937 : CollatzResearch.WordTrace tailWord_4306937 prefixEnd_4306937 2211528829633520822880263 := by
  unfold tailWord_4306937
  simp only [CollatzResearch.WordTrace]
  refine ⟨157086897597710290123287065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104724598398473526748858043 157086897597710290123287065)
  ·
    refine ⟨117815173198282717592465299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157086897597710290123287065 117815173198282717592465299)
    ·
      refine ⟨176722759797424076388697949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117815173198282717592465299 176722759797424076388697949)
      ·
        refine ⟨66271034924034028645761731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176722759797424076388697949 66271034924034028645761731)
        ·
          refine ⟨99406552386051042968642597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66271034924034028645761731 99406552386051042968642597)
          ·
            refine ⟨18638728572384570556620487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99406552386051042968642597 18638728572384570556620487)
            ·
              refine ⟨27958092858576855834930731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18638728572384570556620487 27958092858576855834930731)
              ·
                refine ⟨41937139287865283752396097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27958092858576855834930731 41937139287865283752396097)
                ·
                  refine ⟨31452854465898962814297073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41937139287865283752396097 31452854465898962814297073)
                  ·
                    refine ⟨23589640849424222110722805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31452854465898962814297073 23589640849424222110722805)
                    ·
                      refine ⟨2211528829633520822880263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23589640849424222110722805 2211528829633520822880263)
                      ·
                        rfl

theorem cell23_4306937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_4306937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306937 prefixEnd_4306937 := by exact prefixLift 4306937
  have htrace : WordTrace (prefixWord ++ tailWord_4306937) baseStart_4306937 baseEnd_4306937 := by
    simpa [prefixWord, tailWord_4306937, baseEnd_4306937] using wordTrace_append hprefix tailTrace_4306937
  have hstable : (prefixWord ++ tailWord_4306937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306937).length < 2 ^ (prefixWord ++ tailWord_4306937).sum := by decide
  have hdescent : baseEnd_4306937 < baseStart_4306937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306942 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4306942 : Nat := 118140960795 + 4306942 * 2 ^ 59
def prefixEnd_4306942 : Nat := 4983230072969 + 3 ^ 40 * 4306942 * 2
def baseEnd_4306942 : Nat := 2211531397036793303317741

theorem tailTrace_4306942 : CollatzResearch.WordTrace tailWord_4306942 prefixEnd_4306942 2211531397036793303317741 := by
  unfold tailWord_4306942
  simp only [CollatzResearch.WordTrace]
  refine ⟨19635884995336521997152385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104724719975128117318146053 19635884995336521997152385)
  ·
    refine ⟨14726913746502391497864289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19635884995336521997152385 14726913746502391497864289)
    ·
      refine ⟨11045185309876793623398217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14726913746502391497864289 11045185309876793623398217)
      ·
        refine ⟨8283888982407595217548663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11045185309876793623398217 8283888982407595217548663)
        ·
          refine ⟨12425833473611392826322995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8283888982407595217548663 12425833473611392826322995)
          ·
            refine ⟨18638750210417089239484493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12425833473611392826322995 18638750210417089239484493)
            ·
              refine ⟨6989531328906408464806685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18638750210417089239484493 6989531328906408464806685)
              ·
                refine ⟨2621074248339903174302507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6989531328906408464806685 2621074248339903174302507)
                ·
                  refine ⟨3931611372509854761453761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621074248339903174302507 3931611372509854761453761)
                  ·
                    refine ⟨2948708529382391071090321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3931611372509854761453761 2948708529382391071090321)
                    ·
                      refine ⟨2211531397036793303317741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948708529382391071090321 2211531397036793303317741)
                      ·
                        rfl

theorem cell23_4306942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4306942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306942 prefixEnd_4306942 := by exact prefixLift 4306942
  have htrace : WordTrace (prefixWord ++ tailWord_4306942) baseStart_4306942 baseEnd_4306942 := by
    simpa [prefixWord, tailWord_4306942, baseEnd_4306942] using wordTrace_append hprefix tailTrace_4306942
  have hstable : (prefixWord ++ tailWord_4306942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306942).length < 2 ^ (prefixWord ++ tailWord_4306942).sum := by decide
  have hdescent : baseEnd_4306942 < baseStart_4306942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4306998 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4306998 : Nat := 118140960795 + 4306998 * 2 ^ 59
def prefixEnd_4306998 : Nat := 4983230072969 + 3 ^ 40 * 4306998 * 2
def baseEnd_4306998 : Nat := 2211560151953445084217483

theorem tailTrace_4306998 : CollatzResearch.WordTrace tailWord_4306998 prefixEnd_4306998 2211560151953445084217483 := by
  unfold tailWord_4306998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818070153155581096328603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104726081633659531694171765 9818070153155581096328603)
  ·
    refine ⟨14727105229733371644492905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9818070153155581096328603 14727105229733371644492905)
    ·
      refine ⟨11045328922300028733369679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14727105229733371644492905 11045328922300028733369679)
      ·
        refine ⟨16567993383450043100054519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11045328922300028733369679 16567993383450043100054519)
        ·
          refine ⟨24851990075175064650081779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16567993383450043100054519 24851990075175064650081779)
          ·
            refine ⟨37277985112762596975122669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24851990075175064650081779 37277985112762596975122669)
            ·
              refine ⟨13979244417285973865671001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37277985112762596975122669 13979244417285973865671001)
              ·
                refine ⟨10484433312964480399253251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13979244417285973865671001 10484433312964480399253251)
                ·
                  refine ⟨15726649969446720598879877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10484433312964480399253251 15726649969446720598879877)
                  ·
                    refine ⟨2948746869271260112289977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15726649969446720598879877 2948746869271260112289977)
                    ·
                      refine ⟨2211560151953445084217483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948746869271260112289977 2211560151953445084217483)
                      ·
                        rfl

theorem cell23_4306998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4306998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4306998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4306998 prefixEnd_4306998 := by exact prefixLift 4306998
  have htrace : WordTrace (prefixWord ++ tailWord_4306998) baseStart_4306998 baseEnd_4306998 := by
    simpa [prefixWord, tailWord_4306998, baseEnd_4306998] using wordTrace_append hprefix tailTrace_4306998
  have hstable : (prefixWord ++ tailWord_4306998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4306998).length < 2 ^ (prefixWord ++ tailWord_4306998).sum := by decide
  have hdescent : baseEnd_4306998 < baseStart_4306998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4306998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307027 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_4307027 : Nat := 118140960795 + 4307027 * 2 ^ 59
def prefixEnd_4307027 : Nat := 4983230072969 + 3 ^ 40 * 4307027 * 2
def baseEnd_4307027 : Nat := 2211575042892425470754849

theorem tailTrace_4307027 : CollatzResearch.WordTrace tailWord_4307027 prefixEnd_4307027 2211575042892425470754849 := by
  unfold tailWord_4307027
  simp only [CollatzResearch.WordTrace]
  refine ⟨157090180167384235494063335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104726786778256156996042223 157090180167384235494063335)
  ·
    refine ⟨235635270251076353241095003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157090180167384235494063335 235635270251076353241095003)
    ·
      refine ⟨353452905376614529861642505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235635270251076353241095003 353452905376614529861642505)
      ·
        refine ⟨265089679032460897396231879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353452905376614529861642505 265089679032460897396231879)
        ·
          refine ⟨397634518548691346094347819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265089679032460897396231879 397634518548691346094347819)
          ·
            refine ⟨596451777823037019141521729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397634518548691346094347819 596451777823037019141521729)
            ·
              refine ⟨447338833367277764356141297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596451777823037019141521729 447338833367277764356141297)
              ·
                refine ⟨335504125025458323267105973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447338833367277764356141297 335504125025458323267105973)
                ·
                  refine ⟨31453511721136717806291185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 335504125025458323267105973 31453511721136717806291185)
                  ·
                    refine ⟨23590133790852538354718389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31453511721136717806291185 23590133790852538354718389)
                    ·
                      refine ⟨2211575042892425470754849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23590133790852538354718389 2211575042892425470754849)
                      ·
                        rfl

theorem cell23_4307027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_4307027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307027 prefixEnd_4307027 := by exact prefixLift 4307027
  have htrace : WordTrace (prefixWord ++ tailWord_4307027) baseStart_4307027 baseEnd_4307027 := by
    simpa [prefixWord, tailWord_4307027, baseEnd_4307027] using wordTrace_append hprefix tailTrace_4307027
  have hstable : (prefixWord ++ tailWord_4307027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307027).length < 2 ^ (prefixWord ++ tailWord_4307027).sum := by decide
  have hdescent : baseEnd_4307027 < baseStart_4307027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307064 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_4307064 : Nat := 118140960795 + 4307064 * 2 ^ 59
def prefixEnd_4307064 : Nat := 4983230072969 + 3 ^ 40 * 4307064 * 2
def baseEnd_4307064 : Nat := 737198013892213941997393

theorem tailTrace_4307064 : CollatzResearch.WordTrace tailWord_4307064 prefixEnd_4307064 737198013892213941997393 := by
  unfold tailWord_4307064
  simp only [CollatzResearch.WordTrace]
  refine ⟨78545764834125095406580123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104727686445500127208773497 78545764834125095406580123)
  ·
    refine ⟨117818647251187643109870185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78545764834125095406580123 117818647251187643109870185)
    ·
      refine ⟨88363985438390732332402639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117818647251187643109870185 88363985438390732332402639)
      ·
        refine ⟨132545978157586098498603959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88363985438390732332402639 132545978157586098498603959)
        ·
          refine ⟨198818967236379147747905939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132545978157586098498603959 198818967236379147747905939)
          ·
            refine ⟨298228450854568721621858909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198818967236379147747905939 298228450854568721621858909)
            ·
              refine ⟨111835669070463270608197091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 298228450854568721621858909 111835669070463270608197091)
              ·
                refine ⟨167753503605694905912295637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111835669070463270608197091 167753503605694905912295637)
                ·
                  refine ⟨3931722740758474357319429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167753503605694905912295637 3931722740758474357319429)
                  ·
                    refine ⟨737198013892213941997393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931722740758474357319429 737198013892213941997393)
                    ·
                      rfl

theorem cell23_4307064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_4307064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307064 prefixEnd_4307064 := by exact prefixLift 4307064
  have htrace : WordTrace (prefixWord ++ tailWord_4307064) baseStart_4307064 baseEnd_4307064 := by
    simpa [prefixWord, tailWord_4307064, baseEnd_4307064] using wordTrace_append hprefix tailTrace_4307064
  have hstable : (prefixWord ++ tailWord_4307064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307064).length < 2 ^ (prefixWord ++ tailWord_4307064).sum := by decide
  have hdescent : baseEnd_4307064 < baseStart_4307064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307081 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_4307081 : Nat := 118140960795 + 4307081 * 2 ^ 59
def prefixEnd_4307081 : Nat := 4983230072969 + 3 ^ 40 * 4307081 * 2
def baseEnd_4307081 : Nat := 737200923615922753159867

theorem tailTrace_4307081 : CollatzResearch.WordTrace tailWord_4307081 prefixEnd_4307081 737200923615922753159867 := by
  unfold tailWord_4307081
  simp only [CollatzResearch.WordTrace]
  refine ⟨157092149709188602716529097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104728099806125735144352731 157092149709188602716529097)
  ·
    refine ⟨117819112281891452037396823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157092149709188602716529097 117819112281891452037396823)
    ·
      refine ⟨176728668422837178056095235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117819112281891452037396823 176728668422837178056095235)
      ·
        refine ⟨265093002634255767084142853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176728668422837178056095235 265093002634255767084142853)
        ·
          refine ⟨49704937993922956328276785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265093002634255767084142853 49704937993922956328276785)
          ·
            refine ⟨37278703495442217246207589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49704937993922956328276785 37278703495442217246207589)
            ·
              refine ⟨6989756905395415733663923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37278703495442217246207589 6989756905395415733663923)
              ·
                refine ⟨10484635358093123600495885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989756905395415733663923 10484635358093123600495885)
                ·
                  refine ⟨3931738259284921350185957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10484635358093123600495885 3931738259284921350185957)
                  ·
                    refine ⟨737200923615922753159867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931738259284921350185957 737200923615922753159867)
                    ·
                      rfl

theorem cell23_4307081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_4307081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307081 prefixEnd_4307081 := by exact prefixLift 4307081
  have htrace : WordTrace (prefixWord ++ tailWord_4307081) baseStart_4307081 baseEnd_4307081 := by
    simpa [prefixWord, tailWord_4307081, baseEnd_4307081] using wordTrace_append hprefix tailTrace_4307081
  have hstable : (prefixWord ++ tailWord_4307081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307081).length < 2 ^ (prefixWord ++ tailWord_4307081).sum := by decide
  have hdescent : baseEnd_4307081 < baseStart_4307081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307125 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4307125 : Nat := 118140960795 + 4307125 * 2 ^ 59
def prefixEnd_4307125 : Nat := 4983230072969 + 3 ^ 40 * 4307125 * 2
def baseEnd_4307125 : Nat := 2211625363996566087329399

theorem tailTrace_4307125 : CollatzResearch.WordTrace tailWord_4307125 prefixEnd_4307125 2211625363996566087329399 := by
  unfold tailWord_4307125
  simp only [CollatzResearch.WordTrace]
  refine ⟨157093754521029198231130829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104729169680686132154087219 157093754521029198231130829)
  ·
    refine ⟨58910157945385949336674061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157093754521029198231130829 58910157945385949336674061)
    ·
      refine ⟨22091309229519731001252773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58910157945385949336674061 22091309229519731001252773)
      ·
        refine ⟨4142120480534949562734895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22091309229519731001252773 4142120480534949562734895)
        ·
          refine ⟨6213180720802424344102343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142120480534949562734895 6213180720802424344102343)
          ·
            refine ⟨9319771081203636516153515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213180720802424344102343 9319771081203636516153515)
            ·
              refine ⟨13979656621805454774230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9319771081203636516153515 13979656621805454774230273)
              ·
                refine ⟨10484742466354091080672705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13979656621805454774230273 10484742466354091080672705)
                ·
                  refine ⟨7863556849765568310504529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10484742466354091080672705 7863556849765568310504529)
                  ·
                    refine ⟨5897667637324176232878397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7863556849765568310504529 5897667637324176232878397)
                    ·
                      refine ⟨2211625363996566087329399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5897667637324176232878397 2211625363996566087329399)
                      ·
                        rfl

theorem cell23_4307125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4307125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307125 prefixEnd_4307125 := by exact prefixLift 4307125
  have htrace : WordTrace (prefixWord ++ tailWord_4307125) baseStart_4307125 baseEnd_4307125 := by
    simpa [prefixWord, tailWord_4307125, baseEnd_4307125] using wordTrace_append hprefix tailTrace_4307125
  have hstable : (prefixWord ++ tailWord_4307125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307125).length < 2 ^ (prefixWord ++ tailWord_4307125).sum := by decide
  have hdescent : baseEnd_4307125 < baseStart_4307125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307132 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_4307132 : Nat := 118140960795 + 4307132 * 2 ^ 59
def prefixEnd_4307132 : Nat := 4983230072969 + 3 ^ 40 * 4307132 * 2
def baseEnd_4307132 : Nat := 737209652787049186647289

theorem tailTrace_4307132 : CollatzResearch.WordTrace tailWord_4307132 prefixEnd_4307132 737209652787049186647289 := by
  unfold tailWord_4307132
  simp only [CollatzResearch.WordTrace]
  refine ⟨78547004916001919213317825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104729339888002558951090433 78547004916001919213317825)
  ·
    refine ⟨58910253687001439409988369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78547004916001919213317825 58910253687001439409988369)
    ·
      refine ⟨44182690265251079557491277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58910253687001439409988369 44182690265251079557491277)
      ·
        refine ⟨16568508849469154834059229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44182690265251079557491277 16568508849469154834059229)
        ·
          refine ⟨6213190818550933062772211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16568508849469154834059229 6213190818550933062772211)
          ·
            refine ⟨9319786227826399594158317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213190818550933062772211 9319786227826399594158317)
            ·
              refine ⟨3494919835434899847809369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9319786227826399594158317 3494919835434899847809369)
              ·
                refine ⟨2621189876576174885857027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494919835434899847809369 2621189876576174885857027)
                ·
                  refine ⟨3931784814864262328785541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621189876576174885857027 3931784814864262328785541)
                  ·
                    refine ⟨737209652787049186647289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3931784814864262328785541 737209652787049186647289)
                    ·
                      rfl

theorem cell23_4307132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_4307132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307132 prefixEnd_4307132 := by exact prefixLift 4307132
  have htrace : WordTrace (prefixWord ++ tailWord_4307132) baseStart_4307132 baseEnd_4307132 := by
    simpa [prefixWord, tailWord_4307132, baseEnd_4307132] using wordTrace_append hprefix tailTrace_4307132
  have hstable : (prefixWord ++ tailWord_4307132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307132).length < 2 ^ (prefixWord ++ tailWord_4307132).sum := by decide
  have hdescent : baseEnd_4307132 < baseStart_4307132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307144 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_4307144 : Nat := 118140960795 + 4307144 * 2 ^ 59
def prefixEnd_4307144 : Nat := 4983230072969 + 3 ^ 40 * 4307144 * 2
def baseEnd_4307144 : Nat := 2211635120129001512991811

theorem tailTrace_4307144 : CollatzResearch.WordTrace tailWord_4307144 prefixEnd_4307144 2211635120129001512991811 := by
  unfold tailWord_4307144
  simp only [CollatzResearch.WordTrace]
  refine ⟨78547223753980182238036243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104729631671973576317381657 78547223753980182238036243)
  ·
    refine ⟨117820835630970273357054365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78547223753980182238036243 117820835630970273357054365)
    ·
      refine ⟨44182813361613852508895387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117820835630970273357054365 44182813361613852508895387)
      ·
        refine ⟨66274220042420778763343081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44182813361613852508895387 66274220042420778763343081)
        ·
          refine ⟨49705665031815584072507311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66274220042420778763343081 49705665031815584072507311)
          ·
            refine ⟨74558497547723376108760967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49705665031815584072507311 74558497547723376108760967)
            ·
              refine ⟨111837746321585064163141451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74558497547723376108760967 111837746321585064163141451)
              ·
                refine ⟨167756619482377596244712177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111837746321585064163141451 167756619482377596244712177)
                ·
                  refine ⟨125817464611783197183534133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167756619482377596244712177 125817464611783197183534133)
                  ·
                    refine ⟨11795387307354674735956325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125817464611783197183534133 11795387307354674735956325)
                    ·
                      refine ⟨2211635120129001512991811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11795387307354674735956325 2211635120129001512991811)
                      ·
                        rfl

theorem cell23_4307144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_4307144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307144 prefixEnd_4307144 := by exact prefixLift 4307144
  have htrace : WordTrace (prefixWord ++ tailWord_4307144) baseStart_4307144 baseEnd_4307144 := by
    simpa [prefixWord, tailWord_4307144, baseEnd_4307144] using wordTrace_append hprefix tailTrace_4307144
  have hstable : (prefixWord ++ tailWord_4307144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307144).length < 2 ^ (prefixWord ++ tailWord_4307144).sum := by decide
  have hdescent : baseEnd_4307144 < baseStart_4307144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307161 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 6, 2]
def baseStart_4307161 : Nat := 118140960795 + 4307161 * 2 ^ 59
def prefixEnd_4307161 : Nat := 4983230072969 + 3 ^ 40 * 4307161 * 2
def baseEnd_4307161 : Nat := 2211643849300127946479233

theorem tailTrace_4307161 : CollatzResearch.WordTrace tailWord_4307161 prefixEnd_4307161 2211643849300127946479233 := by
  unfold tailWord_4307161
  simp only [CollatzResearch.WordTrace]
  refine ⟨157095067548898776379441337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104730045032599184252960891 157095067548898776379441337)
  ·
    refine ⟨117821300661674082284581003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157095067548898776379441337 117821300661674082284581003)
    ·
      refine ⟨176731950992511123426871505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117821300661674082284581003 176731950992511123426871505)
      ·
        refine ⟨132548963244383342570153629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176731950992511123426871505 132548963244383342570153629)
        ·
          refine ⟨49705861216643753463807611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132548963244383342570153629 49705861216643753463807611)
          ·
            refine ⟨74558791824965630195711417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49705861216643753463807611 74558791824965630195711417)
            ·
              refine ⟨55919093868724222646783563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74558791824965630195711417 55919093868724222646783563)
              ·
                refine ⟨83878640803086333970175345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55919093868724222646783563 83878640803086333970175345)
                ·
                  refine ⟨62908980602314750477631509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83878640803086333970175345 62908980602314750477631509)
                  ·
                    refine ⟨2948858465733503928638977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62908980602314750477631509 2948858465733503928638977)
                    ·
                      refine ⟨2211643849300127946479233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948858465733503928638977 2211643849300127946479233)
                      ·
                        rfl

theorem cell23_4307161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_4307161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307161 prefixEnd_4307161 := by exact prefixLift 4307161
  have htrace : WordTrace (prefixWord ++ tailWord_4307161) baseStart_4307161 baseEnd_4307161 := by
    simpa [prefixWord, tailWord_4307161, baseEnd_4307161] using wordTrace_append hprefix tailTrace_4307161
  have hstable : (prefixWord ++ tailWord_4307161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307161).length < 2 ^ (prefixWord ++ tailWord_4307161).sum := by decide
  have hdescent : baseEnd_4307161 < baseStart_4307161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307165 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4307165 : Nat := 118140960795 + 4307165 * 2 ^ 59
def prefixEnd_4307165 : Nat := 4983230072969 + 3 ^ 40 * 4307165 * 2
def baseEnd_4307165 : Nat := 2211645903222745930829215

theorem tailTrace_4307165 : CollatzResearch.WordTrace tailWord_4307165 prefixEnd_4307165 2211645903222745930829215 := by
  unfold tailWord_4307165
  simp only [CollatzResearch.WordTrace]
  refine ⟨157095213440884285062586949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104730142293922856708391299 157095213440884285062586949)
  ·
    refine ⟨29455352520165803449235053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157095213440884285062586949 29455352520165803449235053)
    ·
      refine ⟨11045757195062176293463145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29455352520165803449235053 11045757195062176293463145)
      ·
        refine ⟨8284317896296632220097359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11045757195062176293463145 8284317896296632220097359)
        ·
          refine ⟨12426476844444948330146039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8284317896296632220097359 12426476844444948330146039)
          ·
            refine ⟨18639715266667422495219059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12426476844444948330146039 18639715266667422495219059)
            ·
              refine ⟨27959572900001133742828589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18639715266667422495219059 27959572900001133742828589)
              ·
                refine ⟨10484839837500425153560721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27959572900001133742828589 10484839837500425153560721)
                ·
                  refine ⟨7863629878125318865170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10484839837500425153560721 7863629878125318865170541)
                  ·
                    refine ⟨2948861204296994574438953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7863629878125318865170541 2948861204296994574438953)
                    ·
                      refine ⟨2211645903222745930829215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2948861204296994574438953 2211645903222745930829215)
                      ·
                        rfl

theorem cell23_4307165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4307165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307165 prefixEnd_4307165 := by exact prefixLift 4307165
  have htrace : WordTrace (prefixWord ++ tailWord_4307165) baseStart_4307165 baseEnd_4307165 := by
    simpa [prefixWord, tailWord_4307165, baseEnd_4307165] using wordTrace_append hprefix tailTrace_4307165
  have hstable : (prefixWord ++ tailWord_4307165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307165).length < 2 ^ (prefixWord ++ tailWord_4307165).sum := by decide
  have hdescent : baseEnd_4307165 < baseStart_4307165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307175 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 1, 5]
def baseStart_4307175 : Nat := 118140960795 + 4307175 * 2 ^ 59
def prefixEnd_4307175 : Nat := 4983230072969 + 3 ^ 40 * 4307175 * 2
def baseEnd_4307175 : Nat := 737217012676430297234723

theorem tailTrace_4307175 : CollatzResearch.WordTrace tailWord_4307175 prefixEnd_4307175 737217012676430297234723 := by
  unfold tailWord_4307175
  simp only [CollatzResearch.WordTrace]
  refine ⟨157095578170848056770450979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104730385447232037846967319 157095578170848056770450979)
  ·
    refine ⟨235643367256272085155676469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157095578170848056770450979 235643367256272085155676469)
    ·
      refine ⟨22091565680275507983344669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235643367256272085155676469 22091565680275507983344669)
      ·
        refine ⟨8284337130103315493754251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22091565680275507983344669 8284337130103315493754251)
        ·
          refine ⟨12426505695154973240631377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8284337130103315493754251 12426505695154973240631377)
          ·
            refine ⟨9319879271366229930473533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12426505695154973240631377 9319879271366229930473533)
            ·
              refine ⟨3494954726762336223927575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9319879271366229930473533 3494954726762336223927575)
              ·
                refine ⟨5242432090143504335891363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494954726762336223927575 5242432090143504335891363)
                ·
                  refine ⟨7863648135215256503837045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242432090143504335891363 7863648135215256503837045)
                  ·
                    refine ⟨737217012676430297234723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7863648135215256503837045 737217012676430297234723)
                    ·
                      rfl

theorem cell23_4307175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_4307175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307175 prefixEnd_4307175 := by exact prefixLift 4307175
  have htrace : WordTrace (prefixWord ++ tailWord_4307175) baseStart_4307175 baseEnd_4307175 := by
    simpa [prefixWord, tailWord_4307175, baseEnd_4307175] using wordTrace_append hprefix tailTrace_4307175
  have hstable : (prefixWord ++ tailWord_4307175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307175).length < 2 ^ (prefixWord ++ tailWord_4307175).sum := by decide
  have hdescent : baseEnd_4307175 < baseStart_4307175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307198 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_4307198 : Nat := 118140960795 + 4307198 * 2 ^ 59
def prefixEnd_4307198 : Nat := 4983230072969 + 3 ^ 40 * 4307198 * 2
def baseEnd_4307198 : Nat := 2211662848084344301716563

theorem tailTrace_4307198 : CollatzResearch.WordTrace tailWord_4307198 prefixEnd_4307198 2211662848084344301716563 := by
  unfold tailWord_4307198
  simp only [CollatzResearch.WordTrace]
  refine ⟨19637052131220591462317281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104730944699843154465692165 19637052131220591462317281)
  ·
    refine ⟨14727789098415443596737961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19637052131220591462317281 14727789098415443596737961)
    ·
      refine ⟨11045841823811582697553471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14727789098415443596737961 11045841823811582697553471)
      ·
        refine ⟨16568762735717374046330207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11045841823811582697553471 16568762735717374046330207)
        ·
          refine ⟨24853144103576061069495311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16568762735717374046330207 24853144103576061069495311)
          ·
            refine ⟨37279716155364091604242967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24853144103576061069495311 37279716155364091604242967)
            ·
              refine ⟨55919574233046137406364451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37279716155364091604242967 55919574233046137406364451)
              ·
                refine ⟨83879361349569206109546677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55919574233046137406364451 83879361349569206109546677)
                ·
                  refine ⟨7863690126522113072770001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83879361349569206109546677 7863690126522113072770001)
                  ·
                    refine ⟨5897767594891584804577501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7863690126522113072770001 5897767594891584804577501)
                    ·
                      refine ⟨2211662848084344301716563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5897767594891584804577501 2211662848084344301716563)
                      ·
                        rfl

theorem cell23_4307198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_4307198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307198 prefixEnd_4307198 := by exact prefixLift 4307198
  have htrace : WordTrace (prefixWord ++ tailWord_4307198) baseStart_4307198 baseEnd_4307198 := by
    simpa [prefixWord, tailWord_4307198, baseEnd_4307198] using wordTrace_append hprefix tailTrace_4307198
  have hstable : (prefixWord ++ tailWord_4307198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307198).length < 2 ^ (prefixWord ++ tailWord_4307198).sum := by decide
  have hdescent : baseEnd_4307198 < baseStart_4307198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307208 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_4307208 : Nat := 118140960795 + 4307208 * 2 ^ 59
def prefixEnd_4307208 : Nat := 4983230072969 + 3 ^ 40 * 4307208 * 2
def baseEnd_4307208 : Nat := 2211667982890889262591517

theorem tailTrace_4307208 : CollatzResearch.WordTrace tailWord_4307208 prefixEnd_4307208 2211667982890889262591517 := by
  unfold tailWord_4307208
  simp only [CollatzResearch.WordTrace]
  refine ⟨78548390889864251703201139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104731187853152335604268185 78548390889864251703201139)
  ·
    refine ⟨117822586334796377554801709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78548390889864251703201139 117822586334796377554801709)
    ·
      refine ⟨44183469875548641583050641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117822586334796377554801709 44183469875548641583050641)
      ·
        refine ⟨33137602406661481187287981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44183469875548641583050641 33137602406661481187287981)
        ·
          refine ⟨12426600902498055445232993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33137602406661481187287981 12426600902498055445232993)
          ·
            refine ⟨9319950676873541583924745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12426600902498055445232993 9319950676873541583924745)
            ·
              refine ⟨6989963007655156187943559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9319950676873541583924745 6989963007655156187943559)
              ·
                refine ⟨10484944511482734281915339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989963007655156187943559 10484944511482734281915339)
                ·
                  refine ⟨15727416767224101422873009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10484944511482734281915339 15727416767224101422873009)
                  ·
                    refine ⟨11795562575418076067154757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15727416767224101422873009 11795562575418076067154757)
                    ·
                      refine ⟨2211667982890889262591517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11795562575418076067154757 2211667982890889262591517)
                      ·
                        rfl

theorem cell23_4307208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_4307208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307208 prefixEnd_4307208 := by exact prefixLift 4307208
  have htrace : WordTrace (prefixWord ++ tailWord_4307208) baseStart_4307208 baseEnd_4307208 := by
    simpa [prefixWord, tailWord_4307208, baseEnd_4307208] using wordTrace_append hprefix tailTrace_4307208
  have hstable : (prefixWord ++ tailWord_4307208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307208).length < 2 ^ (prefixWord ++ tailWord_4307208).sum := by decide
  have hdescent : baseEnd_4307208 < baseStart_4307208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307228 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4307228 : Nat := 118140960795 + 4307228 * 2 ^ 59
def prefixEnd_4307228 : Nat := 4983230072969 + 3 ^ 40 * 4307228 * 2
def baseEnd_4307228 : Nat := 2211678252503979184341425

theorem tailTrace_4307228 : CollatzResearch.WordTrace tailWord_4307228 prefixEnd_4307228 2211678252503979184341425 := by
  unfold tailWord_4307228
  simp only [CollatzResearch.WordTrace]
  refine ⟨78548755619828023411065169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104731674159770697881420225 78548755619828023411065169)
  ·
    refine ⟨58911566714871017558298877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78548755619828023411065169 58911566714871017558298877)
    ·
      refine ⟨22091837518076631584362079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58911566714871017558298877 22091837518076631584362079)
      ·
        refine ⟨33137756277114947376543119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22091837518076631584362079 33137756277114947376543119)
        ·
          refine ⟨49706634415672421064814679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33137756277114947376543119 49706634415672421064814679)
          ·
            refine ⟨74559951623508631597222019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49706634415672421064814679 74559951623508631597222019)
            ·
              refine ⟨111839927435262947395833029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74559951623508631597222019 111839927435262947395833029)
              ·
                refine ⟨20969986394111802636718693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111839927435262947395833029 20969986394111802636718693)
                ·
                  refine ⟨3931872448895962994384755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20969986394111802636718693 3931872448895962994384755)
                  ·
                    refine ⟨5897808673343944491577133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931872448895962994384755 5897808673343944491577133)
                    ·
                      refine ⟨2211678252503979184341425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5897808673343944491577133 2211678252503979184341425)
                      ·
                        rfl

theorem cell23_4307228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4307228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307228 prefixEnd_4307228 := by exact prefixLift 4307228
  have htrace : WordTrace (prefixWord ++ tailWord_4307228) baseStart_4307228 baseEnd_4307228 := by
    simpa [prefixWord, tailWord_4307228, baseEnd_4307228] using wordTrace_append hprefix tailTrace_4307228
  have hstable : (prefixWord ++ tailWord_4307228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307228).length < 2 ^ (prefixWord ++ tailWord_4307228).sum := by decide
  have hdescent : baseEnd_4307228 < baseStart_4307228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307229 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4307229 : Nat := 118140960795 + 4307229 * 2 ^ 59
def prefixEnd_4307229 : Nat := 4983230072969 + 3 ^ 40 * 4307229 * 2
def baseEnd_4307229 : Nat := 2211678765984633680428921

theorem tailTrace_4307229 : CollatzResearch.WordTrace tailWord_4307229 prefixEnd_4307229 2211678765984633680428921 := by
  unfold tailWord_4307229
  simp only [CollatzResearch.WordTrace]
  refine ⟨157097547712652423992916741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104731698475101615995277827 157097547712652423992916741)
  ·
    refine ⟨29455790196122329498671889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157097547712652423992916741 29455790196122329498671889)
    ·
      refine ⟨22091842647091747124003917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29455790196122329498671889 22091842647091747124003917)
      ·
        refine ⟨8284440992659405171501469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22091842647091747124003917 8284440992659405171501469)
        ·
          refine ⟨3106665372247276939313051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8284440992659405171501469 3106665372247276939313051)
          ·
            refine ⟨4659998058370915408969577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106665372247276939313051 4659998058370915408969577)
            ·
              refine ⟨3494998543778186556727183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4659998058370915408969577 3494998543778186556727183)
              ·
                refine ⟨5242497815667279835090775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494998543778186556727183 5242497815667279835090775)
                ·
                  refine ⟨7863746723500919752636163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242497815667279835090775 7863746723500919752636163)
                  ·
                    refine ⟨11795620085251379628954245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7863746723500919752636163 11795620085251379628954245)
                    ·
                      refine ⟨2211678765984633680428921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11795620085251379628954245 2211678765984633680428921)
                      ·
                        rfl

theorem cell23_4307229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4307229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307229 prefixEnd_4307229 := by exact prefixLift 4307229
  have htrace : WordTrace (prefixWord ++ tailWord_4307229) baseStart_4307229 baseEnd_4307229 := by
    simpa [prefixWord, tailWord_4307229, baseEnd_4307229] using wordTrace_append hprefix tailTrace_4307229
  have hstable : (prefixWord ++ tailWord_4307229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307229).length < 2 ^ (prefixWord ++ tailWord_4307229).sum := by decide
  have hdescent : baseEnd_4307229 < baseStart_4307229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307232 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4307232 : Nat := 118140960795 + 4307232 * 2 ^ 59
def prefixEnd_4307232 : Nat := 4983230072969 + 3 ^ 40 * 4307232 * 2
def baseEnd_4307232 : Nat := 2211680306426597168691407

theorem tailTrace_4307232 : CollatzResearch.WordTrace tailWord_4307232 prefixEnd_4307232 2211680306426597168691407 := by
  unfold tailWord_4307232
  simp only [CollatzResearch.WordTrace]
  refine ⟨78548828565820777752637975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104731771421094370336850633 78548828565820777752637975)
  ·
    refine ⟨117823242848731166628956963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78548828565820777752637975 117823242848731166628956963)
    ·
      refine ⟨176734864273096749943435445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117823242848731166628956963 176734864273096749943435445)
      ·
        refine ⟨16568893525602820307197073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176734864273096749943435445 16568893525602820307197073)
        ·
          refine ⟨12426670144202115230397805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16568893525602820307197073 12426670144202115230397805)
          ·
            refine ⟨4660001304075793211399177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12426670144202115230397805 4660001304075793211399177)
            ·
              refine ⟨3495000978056844908549383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4660001304075793211399177 3495000978056844908549383)
              ·
                refine ⟨5242501467085267362824075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495000978056844908549383 5242501467085267362824075)
                ·
                  refine ⟨7863752200627901044236113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242501467085267362824075 7863752200627901044236113)
                  ·
                    refine ⟨5897814150470925783177085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7863752200627901044236113 5897814150470925783177085)
                    ·
                      refine ⟨2211680306426597168691407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5897814150470925783177085 2211680306426597168691407)
                      ·
                        rfl

theorem cell23_4307232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4307232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307232 prefixEnd_4307232 := by exact prefixLift 4307232
  have htrace : WordTrace (prefixWord ++ tailWord_4307232) baseStart_4307232 baseEnd_4307232 := by
    simpa [prefixWord, tailWord_4307232, baseEnd_4307232] using wordTrace_append hprefix tailTrace_4307232
  have hstable : (prefixWord ++ tailWord_4307232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307232).length < 2 ^ (prefixWord ++ tailWord_4307232).sum := by decide
  have hdescent : baseEnd_4307232 < baseStart_4307232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307271 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_4307271 : Nat := 118140960795 + 4307271 * 2 ^ 59
def prefixEnd_4307271 : Nat := 4983230072969 + 3 ^ 40 * 4307271 * 2
def baseEnd_4307271 : Nat := 2211700332172122516103727

theorem tailTrace_4307271 : CollatzResearch.WordTrace tailWord_4307271 prefixEnd_4307271 2211700332172122516103727 := by
  unfold tailWord_4307271
  simp only [CollatzResearch.WordTrace]
  refine ⟨157099079578500265165945667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104732719719000176777297111 157099079578500265165945667)
  ·
    refine ⟨235648619367750397748918501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157099079578500265165945667 235648619367750397748918501)
    ·
      refine ⟨44184116131453199577922219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235648619367750397748918501 44184116131453199577922219)
      ·
        refine ⟨66276174197179799366883329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44184116131453199577922219 66276174197179799366883329)
        ·
          refine ⟨49707130647884849525162497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66276174197179799366883329 49707130647884849525162497)
          ·
            refine ⟨37280347985913637143871873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49707130647884849525162497 37280347985913637143871873)
            ·
              refine ⟨27960260989435227857903905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37280347985913637143871873 27960260989435227857903905)
              ·
                refine ⟨20970195742076420893427929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27960260989435227857903905 20970195742076420893427929)
                ·
                  refine ⟨15727646806557315670070947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20970195742076420893427929 15727646806557315670070947)
                  ·
                    refine ⟨23591470209835973505106421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15727646806557315670070947 23591470209835973505106421)
                    ·
                      refine ⟨2211700332172122516103727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23591470209835973505106421 2211700332172122516103727)
                      ·
                        rfl

theorem cell23_4307271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_4307271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307271 prefixEnd_4307271 := by exact prefixLift 4307271
  have htrace : WordTrace (prefixWord ++ tailWord_4307271) baseStart_4307271 baseEnd_4307271 := by
    simpa [prefixWord, tailWord_4307271, baseEnd_4307271] using wordTrace_append hprefix tailTrace_4307271
  have hstable : (prefixWord ++ tailWord_4307271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307271).length < 2 ^ (prefixWord ++ tailWord_4307271).sum := by decide
  have hdescent : baseEnd_4307271 < baseStart_4307271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307321 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_4307321 : Nat := 118140960795 + 4307321 * 2 ^ 59
def prefixEnd_4307321 : Nat := 4983230072969 + 3 ^ 40 * 4307321 * 2
def baseEnd_4307321 : Nat := 737242002068282440159499

theorem tailTrace_4307321 : CollatzResearch.WordTrace tailWord_4307321 prefixEnd_4307321 737242002068282440159499 := by
  unfold tailWord_4307321
  simp only [CollatzResearch.WordTrace]
  refine ⟨157100903228319123705265817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104733935485546082470177211 157100903228319123705265817)
  ·
    refine ⟨117825677421239342778949363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157100903228319123705265817 117825677421239342778949363)
    ·
      refine ⟨176738516131859014168424045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117825677421239342778949363 176738516131859014168424045)
      ·
        refine ⟨66276943549447130313159017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176738516131859014168424045 66276943549447130313159017)
        ·
          refine ⟨49707707662085347734869263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66276943549447130313159017 49707707662085347734869263)
          ·
            refine ⟨74561561493128021602303895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49707707662085347734869263 74561561493128021602303895)
            ·
              refine ⟨111842342239692032403455843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74561561493128021602303895 111842342239692032403455843)
              ·
                refine ⟨167763513359538048605183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111842342239692032403455843 167763513359538048605183765)
                ·
                  refine ⟨7863914688728346028367989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 167763513359538048605183765 7863914688728346028367989)
                  ·
                    refine ⟨737242002068282440159499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7863914688728346028367989 737242002068282440159499)
                    ·
                      rfl

theorem cell23_4307321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_4307321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307321 prefixEnd_4307321 := by exact prefixLift 4307321
  have htrace : WordTrace (prefixWord ++ tailWord_4307321) baseStart_4307321 baseEnd_4307321 := by
    simpa [prefixWord, tailWord_4307321, baseEnd_4307321] using wordTrace_append hprefix tailTrace_4307321
  have hstable : (prefixWord ++ tailWord_4307321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307321).length < 2 ^ (prefixWord ++ tailWord_4307321).sum := by decide
  have hdescent : baseEnd_4307321 < baseStart_4307321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307378 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_4307378 : Nat := 118140960795 + 4307378 * 2 ^ 59
def prefixEnd_4307378 : Nat := 4983230072969 + 3 ^ 40 * 4307378 * 2
def baseEnd_4307378 : Nat := 2211755274602153597465735

theorem tailTrace_4307378 : CollatzResearch.WordTrace tailWord_4307378 prefixEnd_4307378 2211755274602153597465735 := by
  unfold tailWord_4307378
  simp only [CollatzResearch.WordTrace]
  refine ⟨39275745547278155610022697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104735321459408414960060525 39275745547278155610022697)
  ·
    refine ⟨29456809160458616707517023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39275745547278155610022697 29456809160458616707517023)
    ·
      refine ⟨44185213740687925061275535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29456809160458616707517023 44185213740687925061275535)
      ·
        refine ⟨66277820611031887591913303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44185213740687925061275535 66277820611031887591913303)
        ·
          refine ⟨99416730916547831387869955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66277820611031887591913303 99416730916547831387869955)
          ·
            refine ⟨149125096374821747081804933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99416730916547831387869955 149125096374821747081804933)
            ·
              refine ⟨27960955570279077577838425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149125096374821747081804933 27960955570279077577838425)
              ·
                refine ⟨20970716677709308183378819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27960955570279077577838425 20970716677709308183378819)
                ·
                  refine ⟨31456075016563962275068229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20970716677709308183378819 31456075016563962275068229)
                  ·
                    refine ⟨5898014065605742926575293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31456075016563962275068229 5898014065605742926575293)
                    ·
                      refine ⟨2211755274602153597465735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898014065605742926575293 2211755274602153597465735)
                      ·
                        rfl

theorem cell23_4307378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_4307378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307378 prefixEnd_4307378 := by exact prefixLift 4307378
  have htrace : WordTrace (prefixWord ++ tailWord_4307378) baseStart_4307378 baseEnd_4307378 := by
    simpa [prefixWord, tailWord_4307378, baseEnd_4307378] using wordTrace_append hprefix tailTrace_4307378
  have hstable : (prefixWord ++ tailWord_4307378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307378).length < 2 ^ (prefixWord ++ tailWord_4307378).sum := by decide
  have hdescent : baseEnd_4307378 < baseStart_4307378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307385 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_4307385 : Nat := 118140960795 + 4307385 * 2 ^ 59
def prefixEnd_4307385 : Nat := 4983230072969 + 3 ^ 40 * 4307385 * 2
def baseEnd_4307385 : Nat := 737252956322245023359401

theorem tailTrace_4307385 : CollatzResearch.WordTrace tailWord_4307385 prefixEnd_4307385 737252956322245023359401 := by
  unfold tailWord_4307385
  simp only [CollatzResearch.WordTrace]
  refine ⟨157103237500087262635595609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104735491666724841757063739 157103237500087262635595609)
  ·
    refine ⟨117827428125065446976696707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157103237500087262635595609 117827428125065446976696707)
    ·
      refine ⟨176741142187598170465045061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117827428125065446976696707 176741142187598170465045061)
      ·
        refine ⟨33138964160174656962195949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176741142187598170465045061 33138964160174656962195949)
        ·
          refine ⟨12427111560065496360823481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33138964160174656962195949 12427111560065496360823481)
          ·
            refine ⟨9320333670049122270617611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12427111560065496360823481 9320333670049122270617611)
            ·
              refine ⟨13980500505073683405926417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320333670049122270617611 13980500505073683405926417)
              ·
                refine ⟨10485375378805262554444813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13980500505073683405926417 10485375378805262554444813)
                ·
                  refine ⟨3932015767051973457916805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10485375378805262554444813 3932015767051973457916805)
                  ·
                    refine ⟨737252956322245023359401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932015767051973457916805 737252956322245023359401)
                    ·
                      rfl

theorem cell23_4307385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_4307385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307385 prefixEnd_4307385 := by exact prefixLift 4307385
  have htrace : WordTrace (prefixWord ++ tailWord_4307385) baseStart_4307385 baseEnd_4307385 := by
    simpa [prefixWord, tailWord_4307385, baseEnd_4307385] using wordTrace_append hprefix tailTrace_4307385
  have hstable : (prefixWord ++ tailWord_4307385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307385).length < 2 ^ (prefixWord ++ tailWord_4307385).sum := by decide
  have hdescent : baseEnd_4307385 < baseStart_4307385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307402 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_4307402 : Nat := 118140960795 + 4307402 * 2 ^ 59
def prefixEnd_4307402 : Nat := 4983230072969 + 3 ^ 40 * 4307402 * 2
def baseEnd_4307402 : Nat := 737255866045953834521875

theorem tailTrace_4307402 : CollatzResearch.WordTrace tailWord_4307402 prefixEnd_4307402 737255866045953834521875 := by
  unfold tailWord_4307402
  simp only [CollatzResearch.WordTrace]
  refine ⟨39275964385256418634741115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104735905027350449692642973 39275964385256418634741115)
  ·
    refine ⟨58913946577884627952111673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39275964385256418634741115 58913946577884627952111673)
    ·
      refine ⟨44185459933413470964083755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58913946577884627952111673 44185459933413470964083755)
      ·
        refine ⟨66278189900120206446125633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44185459933413470964083755 66278189900120206446125633)
        ·
          refine ⟨49708642425090154834594225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66278189900120206446125633 49708642425090154834594225)
          ·
            refine ⟨37281481818817616125945669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49708642425090154834594225 37281481818817616125945669)
            ·
              refine ⟨6990277841028303023614813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37281481818817616125945669 6990277841028303023614813)
              ·
                refine ⟨2621354190385613633855555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6990277841028303023614813 2621354190385613633855555)
                ·
                  refine ⟨3932031285578420450783333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621354190385613633855555 3932031285578420450783333)
                  ·
                    refine ⟨737255866045953834521875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932031285578420450783333 737255866045953834521875)
                    ·
                      rfl

theorem cell23_4307402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_4307402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307402 prefixEnd_4307402 := by exact prefixLift 4307402
  have htrace : WordTrace (prefixWord ++ tailWord_4307402) baseStart_4307402 baseEnd_4307402 := by
    simpa [prefixWord, tailWord_4307402, baseEnd_4307402] using wordTrace_append hprefix tailTrace_4307402
  have hstable : (prefixWord ++ tailWord_4307402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307402).length < 2 ^ (prefixWord ++ tailWord_4307402).sum := by decide
  have hdescent : baseEnd_4307402 < baseStart_4307402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307475 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 2, 4]
def baseStart_4307475 : Nat := 118140960795 + 4307475 * 2 ^ 59
def prefixEnd_4307475 : Nat := 4983230072969 + 3 ^ 40 * 4307475 * 2
def baseEnd_4307475 : Nat := 737268360741879905984263

theorem tailTrace_4307475 : CollatzResearch.WordTrace tailWord_4307475 prefixEnd_4307475 737268360741879905984263 := by
  unfold tailWord_4307475
  simp only [CollatzResearch.WordTrace]
  refine ⟨157106520069761208006371879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104737680046507472004247919 157106520069761208006371879)
  ·
    refine ⟨235659780104641812009557819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157106520069761208006371879 235659780104641812009557819)
    ·
      refine ⟨353489670156962718014336729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235659780104641812009557819 353489670156962718014336729)
      ·
        refine ⟨265117252617722038510752547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353489670156962718014336729 265117252617722038510752547)
        ·
          refine ⟨397675878926583057766128821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265117252617722038510752547 397675878926583057766128821)
          ·
            refine ⟨37282113649367161665574577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 397675878926583057766128821 37282113649367161665574577)
            ·
              refine ⟨27961585237025371249180933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37282113649367161665574577 27961585237025371249180933)
              ·
                refine ⟨5242797231942257109221425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27961585237025371249180933 5242797231942257109221425)
                ·
                  refine ⟨3932097923956692831916069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5242797231942257109221425 3932097923956692831916069)
                  ·
                    refine ⟨737268360741879905984263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932097923956692831916069 737268360741879905984263)
                    ·
                      rfl

theorem cell23_4307475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 4].length) (baseStart_4307475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307475 prefixEnd_4307475 := by exact prefixLift 4307475
  have htrace : WordTrace (prefixWord ++ tailWord_4307475) baseStart_4307475 baseEnd_4307475 := by
    simpa [prefixWord, tailWord_4307475, baseEnd_4307475] using wordTrace_append hprefix tailTrace_4307475
  have hstable : (prefixWord ++ tailWord_4307475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307475).length < 2 ^ (prefixWord ++ tailWord_4307475).sum := by decide
  have hdescent : baseEnd_4307475 < baseStart_4307475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307476 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4307476 : Nat := 118140960795 + 4307476 * 2 ^ 59
def prefixEnd_4307476 : Nat := 4983230072969 + 3 ^ 40 * 4307476 * 2
def baseEnd_4307476 : Nat := 2211805595706294214040285

theorem tailTrace_4307476 : CollatzResearch.WordTrace tailWord_4307476 prefixEnd_4307476 2211805595706294214040285 := by
  unfold tailWord_4307476
  simp only [CollatzResearch.WordTrace]
  refine ⟨78553278271378792588579141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104737704361838390118105521 78553278271378792588579141)
  ·
    refine ⟨14728739675883523610358589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78553278271378792588579141 14728739675883523610358589)
    ·
      refine ⟨5523277378456321353884471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14728739675883523610358589 5523277378456321353884471)
      ·
        refine ⟨8284916067684482030826707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523277378456321353884471 8284916067684482030826707)
        ·
          refine ⟨12427374101526723046240061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8284916067684482030826707 12427374101526723046240061)
          ·
            refine ⟨4660265288072521142340023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12427374101526723046240061 4660265288072521142340023)
            ·
              refine ⟨6990397932108781713510035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660265288072521142340023 6990397932108781713510035)
              ·
                refine ⟨10485596898163172570265053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6990397932108781713510035 10485596898163172570265053)
                ·
                  refine ⟨3932098836811189713849395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10485596898163172570265053 3932098836811189713849395)
                  ·
                    refine ⟨5898148255216784570774093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932098836811189713849395 5898148255216784570774093)
                    ·
                      refine ⟨2211805595706294214040285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898148255216784570774093 2211805595706294214040285)
                      ·
                        rfl

theorem cell23_4307476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4307476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307476 prefixEnd_4307476 := by exact prefixLift 4307476
  have htrace : WordTrace (prefixWord ++ tailWord_4307476) baseStart_4307476 baseEnd_4307476 := by
    simpa [prefixWord, tailWord_4307476, baseEnd_4307476] using wordTrace_append hprefix tailTrace_4307476
  have hstable : (prefixWord ++ tailWord_4307476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307476).length < 2 ^ (prefixWord ++ tailWord_4307476).sum := by decide
  have hdescent : baseEnd_4307476 < baseStart_4307476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307485 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4307485 : Nat := 118140960795 + 4307485 * 2 ^ 59
def prefixEnd_4307485 : Nat := 4983230072969 + 3 ^ 40 * 4307485 * 2
def baseEnd_4307485 : Nat := 2211810217032184678827743

theorem tailTrace_4307485 : CollatzResearch.WordTrace tailWord_4307485 prefixEnd_4307485 2211810217032184678827743 := by
  unfold tailWord_4307485
  simp only [CollatzResearch.WordTrace]
  refine ⟨157106884799724979714235909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104737923199816653142823939 157106884799724979714235909)
  ·
    refine ⟨29457540899948433696419233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157106884799724979714235909 29457540899948433696419233)
    ·
      refine ⟨22093155674961325272314425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29457540899948433696419233 22093155674961325272314425)
      ·
        refine ⟨16569866756220993954235819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22093155674961325272314425 16569866756220993954235819)
        ·
          refine ⟨24854800134331490931353729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16569866756220993954235819 24854800134331490931353729)
          ·
            refine ⟨18641100100748618198515297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24854800134331490931353729 18641100100748618198515297)
            ·
              refine ⟨13980825075561463648886473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18641100100748618198515297 13980825075561463648886473)
              ·
                refine ⟨10485618806671097736664855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13980825075561463648886473 10485618806671097736664855)
                ·
                  refine ⟨15728428210006646604997283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10485618806671097736664855 15728428210006646604997283)
                  ·
                    refine ⟨23592642315009969907495925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15728428210006646604997283 23592642315009969907495925)
                    ·
                      refine ⟨2211810217032184678827743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23592642315009969907495925 2211810217032184678827743)
                      ·
                        rfl

theorem cell23_4307485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4307485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307485 prefixEnd_4307485 := by exact prefixLift 4307485
  have htrace : WordTrace (prefixWord ++ tailWord_4307485) baseStart_4307485 baseEnd_4307485 := by
    simpa [prefixWord, tailWord_4307485, baseEnd_4307485] using wordTrace_append hprefix tailTrace_4307485
  have hstable : (prefixWord ++ tailWord_4307485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307485).length < 2 ^ (prefixWord ++ tailWord_4307485).sum := by decide
  have hdescent : baseEnd_4307485 < baseStart_4307485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307526 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_4307526 : Nat := 118140960795 + 4307526 * 2 ^ 59
def prefixEnd_4307526 : Nat := 4983230072969 + 3 ^ 40 * 4307526 * 2
def baseEnd_4307526 : Nat := 737277089913006339471685

theorem tailTrace_4307526 : CollatzResearch.WordTrace tailWord_4307526 prefixEnd_4307526 737277089913006339471685 := by
  unfold tailWord_4307526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909636881018013866139951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104738920128384295810985621 4909636881018013866139951)
  ·
    refine ⟨7364455321527020799209927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4909636881018013866139951 7364455321527020799209927)
    ·
      refine ⟨11046682982290531198814891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364455321527020799209927 11046682982290531198814891)
      ·
        refine ⟨16570024473435796798222337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046682982290531198814891 16570024473435796798222337)
        ·
          refine ⟨12427518355076847598666753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16570024473435796798222337 12427518355076847598666753)
          ·
            refine ⟨9320638766307635699000065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12427518355076847598666753 9320638766307635699000065)
            ·
              refine ⟨6990479074730726774250049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9320638766307635699000065 6990479074730726774250049)
              ·
                refine ⟨5242859306048045080687537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6990479074730726774250049 5242859306048045080687537)
                ·
                  refine ⟨3932144479536033810515653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5242859306048045080687537 3932144479536033810515653)
                  ·
                    refine ⟨737277089913006339471685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932144479536033810515653 737277089913006339471685)
                    ·
                      rfl

theorem cell23_4307526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_4307526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307526 prefixEnd_4307526 := by exact prefixLift 4307526
  have htrace : WordTrace (prefixWord ++ tailWord_4307526) baseStart_4307526 baseEnd_4307526 := by
    simpa [prefixWord, tailWord_4307526, baseEnd_4307526] using wordTrace_append hprefix tailTrace_4307526
  have hstable : (prefixWord ++ tailWord_4307526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307526).length < 2 ^ (prefixWord ++ tailWord_4307526).sum := by decide
  have hdescent : baseEnd_4307526 < baseStart_4307526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307528 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_4307528 : Nat := 118140960795 + 4307528 * 2 ^ 59
def prefixEnd_4307528 : Nat := 4983230072969 + 3 ^ 40 * 4307528 * 2
def baseEnd_4307528 : Nat := 2211832296700328010590045

theorem tailTrace_4307528 : CollatzResearch.WordTrace tailWord_4307528 prefixEnd_4307528 2211832296700328010590045 := by
  unfold tailWord_4307528
  simp only [CollatzResearch.WordTrace]
  refine ⟨78554226569284599029025619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104738968759046132038700825 78554226569284599029025619)
  ·
    refine ⟨117831339853926898543538429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78554226569284599029025619 117831339853926898543538429)
    ·
      refine ⟨44186752445222586953826911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117831339853926898543538429 44186752445222586953826911)
      ·
        refine ⟨66280128667833880430740367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44186752445222586953826911 66280128667833880430740367)
        ·
          refine ⟨99420193001750820646110551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66280128667833880430740367 99420193001750820646110551)
          ·
            refine ⟨149130289502626230969165827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99420193001750820646110551 149130289502626230969165827)
            ·
              refine ⟨223695434253939346453748741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149130289502626230969165827 223695434253939346453748741)
              ·
                refine ⟨41942893922613627460077889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223695434253939346453748741 41942893922613627460077889)
                ·
                  refine ⟨31457170441960220595058417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41942893922613627460077889 31457170441960220595058417)
                  ·
                    refine ⟨23592877831470165446293813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31457170441960220595058417 23592877831470165446293813)
                    ·
                      refine ⟨2211832296700328010590045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23592877831470165446293813 2211832296700328010590045)
                      ·
                        rfl

theorem cell23_4307528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_4307528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307528 prefixEnd_4307528 := by exact prefixLift 4307528
  have htrace : WordTrace (prefixWord ++ tailWord_4307528) baseStart_4307528 baseEnd_4307528 := by
    simpa [prefixWord, tailWord_4307528, baseEnd_4307528] using wordTrace_append hprefix tailTrace_4307528
  have hstable : (prefixWord ++ tailWord_4307528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307528).length < 2 ^ (prefixWord ++ tailWord_4307528).sum := by decide
  have hdescent : baseEnd_4307528 < baseStart_4307528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307533 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4307533 : Nat := 118140960795 + 4307533 * 2 ^ 59
def prefixEnd_4307533 : Nat := 4983230072969 + 3 ^ 40 * 4307533 * 2
def baseEnd_4307533 : Nat := 2211834864103600491027523

theorem tailTrace_4307533 : CollatzResearch.WordTrace tailWord_4307533 prefixEnd_4307533 2211834864103600491027523 := by
  unfold tailWord_4307533
  simp only [CollatzResearch.WordTrace]
  refine ⟨157108635503551083911983253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104739090335700722607988835 157108635503551083911983253)
  ·
    refine ⟨7364467289228957058374215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157108635503551083911983253 7364467289228957058374215)
    ·
      refine ⟨11046700933843435587561323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364467289228957058374215 11046700933843435587561323)
      ·
        refine ⟨16570051400765153381341985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046700933843435587561323 16570051400765153381341985)
        ·
          refine ⟨12427538550573865036006489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16570051400765153381341985 12427538550573865036006489)
          ·
            refine ⟨9320653912930398777004867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12427538550573865036006489 9320653912930398777004867)
            ·
              refine ⟨13980980869395598165507301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320653912930398777004867 13980980869395598165507301)
              ·
                refine ⟨2621433913011674656032619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13980980869395598165507301 2621433913011674656032619)
                ·
                  refine ⟨3932150869517511984048929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621433913011674656032619 3932150869517511984048929)
                  ·
                    refine ⟨2949113152138133988036697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932150869517511984048929 2949113152138133988036697)
                    ·
                      refine ⟨2211834864103600491027523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949113152138133988036697 2211834864103600491027523)
                      ·
                        rfl

theorem cell23_4307533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4307533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307533 prefixEnd_4307533 := by exact prefixLift 4307533
  have htrace : WordTrace (prefixWord ++ tailWord_4307533) baseStart_4307533 baseEnd_4307533 := by
    simpa [prefixWord, tailWord_4307533, baseEnd_4307533] using wordTrace_append hprefix tailTrace_4307533
  have hstable : (prefixWord ++ tailWord_4307533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307533).length < 2 ^ (prefixWord ++ tailWord_4307533).sum := by decide
  have hdescent : baseEnd_4307533 < baseStart_4307533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307550 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4307550 : Nat := 118140960795 + 4307550 * 2 ^ 59
def prefixEnd_4307550 : Nat := 4983230072969 + 3 ^ 40 * 4307550 * 2
def baseEnd_4307550 : Nat := 2211843593274726924514945

theorem tailTrace_4307550 : CollatzResearch.WordTrace tailWord_4307550 prefixEnd_4307550 2211843593274726924514945 := by
  unfold tailWord_4307550
  simp only [CollatzResearch.WordTrace]
  refine ⟨19638656943061186976919013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104739503696326330543568069 19638656943061186976919013)
  ·
    refine ⟨3682248176823972558172315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19638656943061186976919013 3682248176823972558172315)
    ·
      refine ⟨5523372265235958837258473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682248176823972558172315 5523372265235958837258473)
      ·
        refine ⟨4142529198926969127943855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5523372265235958837258473 4142529198926969127943855)
        ·
          refine ⟨6213793798390453691915783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142529198926969127943855 6213793798390453691915783)
          ·
            refine ⟨9320690697585680537873675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213793798390453691915783 9320690697585680537873675)
            ·
              refine ⟨13981036046378520806810513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320690697585680537873675 13981036046378520806810513)
              ·
                refine ⟨10485777034783890605107885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13981036046378520806810513 10485777034783890605107885)
                ·
                  refine ⟨3932166388043958976915457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10485777034783890605107885 3932166388043958976915457)
                  ·
                    refine ⟨2949124791032969232686593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932166388043958976915457 2949124791032969232686593)
                    ·
                      refine ⟨2211843593274726924514945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949124791032969232686593 2211843593274726924514945)
                      ·
                        rfl

theorem cell23_4307550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4307550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307550 prefixEnd_4307550 := by exact prefixLift 4307550
  have htrace : WordTrace (prefixWord ++ tailWord_4307550) baseStart_4307550 baseEnd_4307550 := by
    simpa [prefixWord, tailWord_4307550, baseEnd_4307550] using wordTrace_append hprefix tailTrace_4307550
  have hstable : (prefixWord ++ tailWord_4307550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307550).length < 2 ^ (prefixWord ++ tailWord_4307550).sum := by decide
  have hdescent : baseEnd_4307550 < baseStart_4307550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307585 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4307585 : Nat := 118140960795 + 4307585 * 2 ^ 59
def prefixEnd_4307585 : Nat := 4983230072969 + 3 ^ 40 * 4307585 * 2
def baseEnd_4307585 : Nat := 2211861565097634287577283

theorem tailTrace_4307585 : CollatzResearch.WordTrace tailWord_4307585 prefixEnd_4307585 2211861565097634287577283 := by
  unfold tailWord_4307585
  simp only [CollatzResearch.WordTrace]
  refine ⟨157110532099362696792876209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104740354732908464528584139 157110532099362696792876209)
  ·
    refine ⟨117832899074522022594657157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157110532099362696792876209 117832899074522022594657157)
    ·
      refine ⟨22093668576472879236498217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117832899074522022594657157 22093668576472879236498217)
      ·
        refine ⟨16570251432354659427373663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22093668576472879236498217 16570251432354659427373663)
        ·
          refine ⟨24855377148531989141060495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16570251432354659427373663 24855377148531989141060495)
          ·
            refine ⟨37283065722797983711590743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24855377148531989141060495 37283065722797983711590743)
            ·
              refine ⟨55924598584196975567386115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37283065722797983711590743 55924598584196975567386115)
              ·
                refine ⟨83886897876295463351079173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55924598584196975567386115 83886897876295463351079173)
                ·
                  refine ⟨15728793351805399378327345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83886897876295463351079173 15728793351805399378327345)
                  ·
                    refine ⟨11796595013854049533745509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15728793351805399378327345 11796595013854049533745509)
                    ·
                      refine ⟨2211861565097634287577283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11796595013854049533745509 2211861565097634287577283)
                      ·
                        rfl

theorem cell23_4307585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4307585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307585 prefixEnd_4307585 := by exact prefixLift 4307585
  have htrace : WordTrace (prefixWord ++ tailWord_4307585) baseStart_4307585 baseEnd_4307585 := by
    simpa [prefixWord, tailWord_4307585, baseEnd_4307585] using wordTrace_append hprefix tailTrace_4307585
  have hstable : (prefixWord ++ tailWord_4307585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307585).length < 2 ^ (prefixWord ++ tailWord_4307585).sum := by decide
  have hdescent : baseEnd_4307585 < baseStart_4307585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307589 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_4307589 : Nat := 118140960795 + 4307589 * 2 ^ 59
def prefixEnd_4307589 : Nat := 4983230072969 + 3 ^ 40 * 4307589 * 2
def baseEnd_4307589 : Nat := 2211863619020252271927265

theorem tailTrace_4307589 : CollatzResearch.WordTrace tailWord_4307589 prefixEnd_4307589 2211863619020252271927265 := by
  unfold tailWord_4307589
  simp only [CollatzResearch.WordTrace]
  refine ⟨157110677991348205476021821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104740451994232136984014547 157110677991348205476021821)
  ·
    refine ⟨58916504246755577053508183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157110677991348205476021821 58916504246755577053508183)
    ·
      refine ⟨88374756370133365580262275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58916504246755577053508183 88374756370133365580262275)
      ·
        refine ⟨132562134555200048370393413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88374756370133365580262275 132562134555200048370393413)
        ·
          refine ⟨24855400229100009069448765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132562134555200048370393413 24855400229100009069448765)
          ·
            refine ⟨9320775085912503401043287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24855400229100009069448765 9320775085912503401043287)
            ·
              refine ⟨13981162628868755101564931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320775085912503401043287 13981162628868755101564931)
              ·
                refine ⟨20971743943303132652347397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13981162628868755101564931 20971743943303132652347397)
                ·
                  refine ⟨3932201989369337372315137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20971743943303132652347397 3932201989369337372315137)
                  ·
                    refine ⟨2949151492027003029236353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932201989369337372315137 2949151492027003029236353)
                    ·
                      refine ⟨2211863619020252271927265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949151492027003029236353 2211863619020252271927265)
                      ·
                        rfl

theorem cell23_4307589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_4307589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307589 prefixEnd_4307589 := by exact prefixLift 4307589
  have htrace : WordTrace (prefixWord ++ tailWord_4307589) baseStart_4307589 baseEnd_4307589 := by
    simpa [prefixWord, tailWord_4307589, baseEnd_4307589] using wordTrace_append hprefix tailTrace_4307589
  have hstable : (prefixWord ++ tailWord_4307589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307589).length < 2 ^ (prefixWord ++ tailWord_4307589).sum := by decide
  have hdescent : baseEnd_4307589 < baseStart_4307589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307602 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4307602 : Nat := 118140960795 + 4307602 * 2 ^ 59
def prefixEnd_4307602 : Nat := 4983230072969 + 3 ^ 40 * 4307602 * 2
def baseEnd_4307602 : Nat := 2211870294268760721064705

theorem tailTrace_4307602 : CollatzResearch.WordTrace tailWord_4307602 prefixEnd_4307602 2211870294268760721064705 := by
  unfold tailWord_4307602
  simp only [CollatzResearch.WordTrace]
  refine ⟨39277788035075277174061265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104740768093534072464163373 39277788035075277174061265)
  ·
    refine ⟨29458341026306457880545949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39277788035075277174061265 29458341026306457880545949)
    ·
      refine ⟨11046877884864921705204731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29458341026306457880545949 11046877884864921705204731)
      ·
        refine ⟨16570316827297382557807097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046877884864921705204731 16570316827297382557807097)
        ·
          refine ⟨12427737620473036918355323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16570316827297382557807097 12427737620473036918355323)
          ·
            refine ⟨18641606430709555377532985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12427737620473036918355323 18641606430709555377532985)
            ·
              refine ⟨13981204823032166533149739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18641606430709555377532985 13981204823032166533149739)
              ·
                refine ⟨20971807234548249799724609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13981204823032166533149739 20971807234548249799724609)
                ·
                  refine ⟨15728855425911187349793457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20971807234548249799724609 15728855425911187349793457)
                  ·
                    refine ⟨11796641569433390512345093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15728855425911187349793457 11796641569433390512345093)
                    ·
                      refine ⟨2211870294268760721064705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11796641569433390512345093 2211870294268760721064705)
                      ·
                        rfl

theorem cell23_4307602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4307602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307602 prefixEnd_4307602 := by exact prefixLift 4307602
  have htrace : WordTrace (prefixWord ++ tailWord_4307602) baseStart_4307602 baseEnd_4307602 := by
    simpa [prefixWord, tailWord_4307602, baseEnd_4307602] using wordTrace_append hprefix tailTrace_4307602
  have hstable : (prefixWord ++ tailWord_4307602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307602).length < 2 ^ (prefixWord ++ tailWord_4307602).sum := by decide
  have hdescent : baseEnd_4307602 < baseStart_4307602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307629 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 5]
def baseStart_4307629 : Nat := 118140960795 + 4307629 * 2 ^ 59
def prefixEnd_4307629 : Nat := 4983230072969 + 3 ^ 40 * 4307629 * 2
def baseEnd_4307629 : Nat := 245764906471825790603009

theorem tailTrace_4307629 : CollatzResearch.WordTrace tailWord_4307629 prefixEnd_4307629 245764906471825790603009 := by
  unfold tailWord_4307629
  simp only [CollatzResearch.WordTrace]
  refine ⟨157112136911203292307477941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104741424607468861538318627 157112136911203292307477941)
  ·
    refine ⟨14729262835425308653826057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157112136911203292307477941 14729262835425308653826057)
    ·
      refine ⟨11046947126568981490369543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14729262835425308653826057 11046947126568981490369543)
      ·
        refine ⟨16570420689853472235554315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046947126568981490369543 16570420689853472235554315)
        ·
          refine ⟨24855631034780208353331473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16570420689853472235554315 24855631034780208353331473)
          ·
            refine ⟨18641723276085156264998605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24855631034780208353331473 18641723276085156264998605)
            ·
              refine ⟨6990646228531933599374477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18641723276085156264998605 6990646228531933599374477)
              ·
                refine ⟨2621492335699475099765429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6990646228531933599374477 2621492335699475099765429)
                ·
                  refine ⟨245764906471825790603009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621492335699475099765429 245764906471825790603009)
                  ·
                    rfl

theorem cell23_4307629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_4307629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307629 prefixEnd_4307629 := by exact prefixLift 4307629
  have htrace : WordTrace (prefixWord ++ tailWord_4307629) baseStart_4307629 baseEnd_4307629 := by
    simpa [prefixWord, tailWord_4307629, baseEnd_4307629] using wordTrace_append hprefix tailTrace_4307629
  have hstable : (prefixWord ++ tailWord_4307629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307629).length < 2 ^ (prefixWord ++ tailWord_4307629).sum := by decide
  have hdescent : baseEnd_4307629 < baseStart_4307629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307652 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4307652 : Nat := 118140960795 + 4307652 * 2 ^ 59
def prefixEnd_4307652 : Nat := 4983230072969 + 3 ^ 40 * 4307652 * 2
def baseEnd_4307652 : Nat := 2211895968301485525439475

theorem tailTrace_4307652 : CollatzResearch.WordTrace tailWord_4307652 prefixEnd_4307652 2211895968301485525439475 := by
  unfold tailWord_4307652
  simp only [CollatzResearch.WordTrace]
  refine ⟨78556487895059983617782605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104741983860079978157043473 78556487895059983617782605)
  ·
    refine ⟨29458682960647493856668477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78556487895059983617782605 29458682960647493856668477)
    ·
      refine ⟨11047006110242810196250679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29458682960647493856668477 11047006110242810196250679)
      ·
        refine ⟨16570509165364215294376019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11047006110242810196250679 16570509165364215294376019)
        ·
          refine ⟨24855763748046322941564029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16570509165364215294376019 24855763748046322941564029)
          ·
            refine ⟨9320911405517371103086511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24855763748046322941564029 9320911405517371103086511)
            ·
              refine ⟨13981367108276056654629767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320911405517371103086511 13981367108276056654629767)
              ·
                refine ⟨20972050662414084981944651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13981367108276056654629767 20972050662414084981944651)
                ·
                  refine ⟨31458075993621127472916977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20972050662414084981944651 31458075993621127472916977)
                  ·
                    refine ⟨23593556995215845604687733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31458075993621127472916977 23593556995215845604687733)
                    ·
                      refine ⟨2211895968301485525439475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23593556995215845604687733 2211895968301485525439475)
                      ·
                        rfl

theorem cell23_4307652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4307652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307652 prefixEnd_4307652 := by exact prefixLift 4307652
  have htrace : WordTrace (prefixWord ++ tailWord_4307652) baseStart_4307652 baseEnd_4307652 := by
    simpa [prefixWord, tailWord_4307652, baseEnd_4307652] using wordTrace_append hprefix tailTrace_4307652
  have hstable : (prefixWord ++ tailWord_4307652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307652).length < 2 ^ (prefixWord ++ tailWord_4307652).sum := by decide
  have hdescent : baseEnd_4307652 < baseStart_4307652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307706 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_4307706 : Nat := 118140960795 + 4307706 * 2 ^ 59
def prefixEnd_4307706 : Nat := 4983230072969 + 3 ^ 40 * 4307706 * 2
def baseEnd_4307706 : Nat := 737307898752276104721409

theorem tailTrace_4307706 : CollatzResearch.WordTrace tailWord_4307706 prefixEnd_4307706 737307898752276104721409 := by
  unfold tailWord_4307706
  simp only [CollatzResearch.WordTrace]
  refine ⟨39278736332981083614507743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104743296887949556305353981 39278736332981083614507743)
  ·
    refine ⟨58918104499471625421761615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39278736332981083614507743 58918104499471625421761615)
    ·
      refine ⟨88377156749207438132642423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58918104499471625421761615 88377156749207438132642423)
      ·
        refine ⟨132565735123811157198963635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88377156749207438132642423 132565735123811157198963635)
        ·
          refine ⟨198848602685716735798445453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132565735123811157198963635 198848602685716735798445453)
          ·
            refine ⟨74568226007143775924417045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198848602685716735798445453 74568226007143775924417045)
            ·
              refine ⟨3495385594084864496457049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74568226007143775924417045 3495385594084864496457049)
              ·
                refine ⟨2621539195563648372342787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495385594084864496457049 2621539195563648372342787)
                ·
                  refine ⟨3932308793345472558514181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621539195563648372342787 3932308793345472558514181)
                  ·
                    refine ⟨737307898752276104721409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932308793345472558514181 737307898752276104721409)
                    ·
                      rfl

theorem cell23_4307706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_4307706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307706 prefixEnd_4307706 := by exact prefixLift 4307706
  have htrace : WordTrace (prefixWord ++ tailWord_4307706) baseStart_4307706 baseEnd_4307706 := by
    simpa [prefixWord, tailWord_4307706, baseEnd_4307706] using wordTrace_append hprefix tailTrace_4307706
  have hstable : (prefixWord ++ tailWord_4307706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307706).length < 2 ^ (prefixWord ++ tailWord_4307706).sum := by decide
  have hdescent : baseEnd_4307706 < baseStart_4307706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307792 : List Nat := [2, 1, 1, 1, 1, 4, 6, 7]
def baseStart_4307792 : Nat := 118140960795 + 4307792 * 2 ^ 59
def prefixEnd_4307792 : Nat := 4983230072969 + 3 ^ 40 * 4307792 * 2
def baseEnd_4307792 : Nat := 81924735392337591766253

theorem tailTrace_4307792 : CollatzResearch.WordTrace tailWord_4307792 prefixEnd_4307792 81924735392337591766253 := by
  unfold tailWord_4307792
  simp only [CollatzResearch.WordTrace]
  refine ⟨78559041004806385572830815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104745388006408514097107753 78559041004806385572830815)
  ·
    refine ⟨117838561507209578359246223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78559041004806385572830815 117838561507209578359246223)
    ·
      refine ⟨176757842260814367538869335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117838561507209578359246223 176757842260814367538869335)
      ·
        refine ⟨265136763391221551308304003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176757842260814367538869335 265136763391221551308304003)
        ·
          refine ⟨397705145086832326962456005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265136763391221551308304003 397705145086832326962456005)
          ·
            refine ⟨74569714703781061305460501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 397705145086832326962456005 74569714703781061305460501)
            ·
              refine ⟨3495455376739737248693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74569714703781061305460501 3495455376739737248693461)
              ·
                refine ⟨81924735392337591766253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3495455376739737248693461 81924735392337591766253)
                ·
                  rfl

theorem cell23_4307792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 7].length) (baseStart_4307792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307792 prefixEnd_4307792 := by exact prefixLift 4307792
  have htrace : WordTrace (prefixWord ++ tailWord_4307792) baseStart_4307792 baseEnd_4307792 := by
    simpa [prefixWord, tailWord_4307792, baseEnd_4307792] using wordTrace_append hprefix tailTrace_4307792
  have hstable : (prefixWord ++ tailWord_4307792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307792).length < 2 ^ (prefixWord ++ tailWord_4307792).sum := by decide
  have hdescent : baseEnd_4307792 < baseStart_4307792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_4307795 : Nat := 118140960795 + 4307795 * 2 ^ 59
def prefixEnd_4307795 : Nat := 4983230072969 + 3 ^ 40 * 4307795 * 2
def baseEnd_4307795 : Nat := 2211969396035078465951317

theorem tailTrace_4307795 : CollatzResearch.WordTrace tailWord_4307795 prefixEnd_4307795 2211969396035078465951317 := by
  unfold tailWord_4307795
  simp only [CollatzResearch.WordTrace]
  refine ⟨157118191428601902658020839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104745460952401268438680559 157118191428601902658020839)
  ·
    refine ⟨235677287142902853987031259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157118191428601902658020839 235677287142902853987031259)
    ·
      refine ⟨353515930714354280980546889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235677287142902853987031259 353515930714354280980546889)
      ·
        refine ⟨265136948035765710735410167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353515930714354280980546889 265136948035765710735410167)
        ·
          refine ⟨397705422053648566103115251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265136948035765710735410167 397705422053648566103115251)
          ·
            refine ⟨596558133080472849154672877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397705422053648566103115251 596558133080472849154672877)
            ·
              refine ⟨223709299905177318433002329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 596558133080472849154672877 223709299905177318433002329)
              ·
                refine ⟨167781974928882988824751747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223709299905177318433002329 167781974928882988824751747)
                ·
                  refine ⟨251672962393324483237127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167781974928882988824751747 251672962393324483237127621)
                  ·
                    refine ⟨47188680448748340606961429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251672962393324483237127621 47188680448748340606961429)
                    ·
                      refine ⟨2211969396035078465951317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47188680448748340606961429 2211969396035078465951317)
                      ·
                        rfl

theorem cell23_4307795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_4307795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307795 prefixEnd_4307795 := by exact prefixLift 4307795
  have htrace : WordTrace (prefixWord ++ tailWord_4307795) baseStart_4307795 baseEnd_4307795 := by
    simpa [prefixWord, tailWord_4307795, baseEnd_4307795] using wordTrace_append hprefix tailTrace_4307795
  have hstable : (prefixWord ++ tailWord_4307795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307795).length < 2 ^ (prefixWord ++ tailWord_4307795).sum := by decide
  have hdescent : baseEnd_4307795 < baseStart_4307795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307819 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 3]
def baseStart_4307819 : Nat := 118140960795 + 4307819 * 2 ^ 59
def prefixEnd_4307819 : Nat := 4983230072969 + 3 ^ 40 * 4307819 * 2
def baseEnd_4307819 : Nat := 2211981719570786372051207

theorem tailTrace_4307819 : CollatzResearch.WordTrace tailWord_4307819 prefixEnd_4307819 2211981719570786372051207 := by
  unfold tailWord_4307819
  simp only [CollatzResearch.WordTrace]
  refine ⟨157119066780514954756894511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104746044520343303171263007 157119066780514954756894511)
  ·
    refine ⟨235678600170772432135341767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157119066780514954756894511 235678600170772432135341767)
    ·
      refine ⟨353517900256158648203012651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235678600170772432135341767 353517900256158648203012651)
      ·
        refine ⟨530276850384237972304518977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353517900256158648203012651 530276850384237972304518977)
        ·
          refine ⟨397707637788178479228389233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530276850384237972304518977 397707637788178479228389233)
          ·
            refine ⟨298280728341133859421291925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397707637788178479228389233 298280728341133859421291925)
            ·
              refine ⟨13981909140990649660373059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 298280728341133859421291925 13981909140990649660373059)
              ·
                refine ⟨20972863711485974490559589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13981909140990649660373059 20972863711485974490559589)
                ·
                  refine ⟨3932411945903620216979923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20972863711485974490559589 3932411945903620216979923)
                  ·
                    refine ⟨5898617918855430325469885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932411945903620216979923 5898617918855430325469885)
                    ·
                      refine ⟨2211981719570786372051207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898617918855430325469885 2211981719570786372051207)
                      ·
                        rfl

theorem cell23_4307819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 3].length) (baseStart_4307819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307819 prefixEnd_4307819 := by exact prefixLift 4307819
  have htrace : WordTrace (prefixWord ++ tailWord_4307819) baseStart_4307819 baseEnd_4307819 := by
    simpa [prefixWord, tailWord_4307819, baseEnd_4307819] using wordTrace_append hprefix tailTrace_4307819
  have hstable : (prefixWord ++ tailWord_4307819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307819).length < 2 ^ (prefixWord ++ tailWord_4307819).sum := by decide
  have hdescent : baseEnd_4307819 < baseStart_4307819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307820 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 1, 2, 2]
def baseStart_4307820 : Nat := 118140960795 + 4307820 * 2 ^ 59
def prefixEnd_4307820 : Nat := 4983230072969 + 3 ^ 40 * 4307820 * 2
def baseEnd_4307820 : Nat := 2211982233051440868138703

theorem tailTrace_4307820 : CollatzResearch.WordTrace tailWord_4307820 prefixEnd_4307820 2211982233051440868138703 := by
  unfold tailWord_4307820
  simp only [CollatzResearch.WordTrace]
  refine ⟨78559551626755665963840457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104746068835674221285120609 78559551626755665963840457)
  ·
    refine ⟨58919663720066749472880343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78559551626755665963840457 58919663720066749472880343)
    ·
      refine ⟨88379495580100124209320515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58919663720066749472880343 88379495580100124209320515)
      ·
        refine ⟨132569243370150186313980773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88379495580100124209320515 132569243370150186313980773)
        ·
          refine ⟨24856733131903159933871395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132569243370150186313980773 24856733131903159933871395)
          ·
            refine ⟨37285099697854739900807093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24856733131903159933871395 37285099697854739900807093)
            ·
              refine ⟨3495478096673881865700665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37285099697854739900807093 3495478096673881865700665)
              ·
                refine ⟨2621608572505411399275499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495478096673881865700665 2621608572505411399275499)
                ·
                  refine ⟨3932412858758117098913249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621608572505411399275499 3932412858758117098913249)
                  ·
                    refine ⟨2949309644068587824184937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932412858758117098913249 2949309644068587824184937)
                    ·
                      refine ⟨2211982233051440868138703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949309644068587824184937 2211982233051440868138703)
                      ·
                        rfl

theorem cell23_4307820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_4307820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307820 prefixEnd_4307820 := by exact prefixLift 4307820
  have htrace : WordTrace (prefixWord ++ tailWord_4307820) baseStart_4307820 baseEnd_4307820 := by
    simpa [prefixWord, tailWord_4307820, baseEnd_4307820] using wordTrace_append hprefix tailTrace_4307820
  have hstable : (prefixWord ++ tailWord_4307820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307820).length < 2 ^ (prefixWord ++ tailWord_4307820).sum := by decide
  have hdescent : baseEnd_4307820 < baseStart_4307820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307830 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_4307830 : Nat := 118140960795 + 4307830 * 2 ^ 59
def prefixEnd_4307830 : Nat := 4983230072969 + 3 ^ 40 * 4307830 * 2
def baseEnd_4307830 : Nat := 737329122619328609671219

theorem tailTrace_4307830 : CollatzResearch.WordTrace tailWord_4307830 prefixEnd_4307830 737329122619328609671219 := by
  unfold tailWord_4307830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9819966748967193977221559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104746311988983402423696629 9819966748967193977221559)
  ·
    refine ⟨14729950123450790965832339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9819966748967193977221559 14729950123450790965832339)
    ·
      refine ⟨22094925185176186448748509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14729950123450790965832339 22094925185176186448748509)
      ·
        refine ⟨8285596944441069918280691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22094925185176186448748509 8285596944441069918280691)
        ·
          refine ⟨12428395416661604877421037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285596944441069918280691 12428395416661604877421037)
          ·
            refine ⟨4660648281248101829032889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12428395416661604877421037 4660648281248101829032889)
            ·
              refine ⟨3495486210936076371774667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4660648281248101829032889 3495486210936076371774667)
              ·
                refine ⟨5243229316404114557662001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495486210936076371774667 5243229316404114557662001)
                ·
                  refine ⟨3932421987303085918246501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243229316404114557662001 3932421987303085918246501)
                  ·
                    refine ⟨737329122619328609671219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932421987303085918246501 737329122619328609671219)
                    ·
                      rfl

theorem cell23_4307830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_4307830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307830 prefixEnd_4307830 := by exact prefixLift 4307830
  have htrace : WordTrace (prefixWord ++ tailWord_4307830) baseStart_4307830 baseEnd_4307830 := by
    simpa [prefixWord, tailWord_4307830, baseEnd_4307830] using wordTrace_append hprefix tailTrace_4307830
  have hstable : (prefixWord ++ tailWord_4307830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307830).length < 2 ^ (prefixWord ++ tailWord_4307830).sum := by decide
  have hdescent : baseEnd_4307830 < baseStart_4307830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307863 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_4307863 : Nat := 118140960795 + 4307863 * 2 ^ 59
def prefixEnd_4307863 : Nat := 4983230072969 + 3 ^ 40 * 4307863 * 2
def baseEnd_4307863 : Nat := 2212004312719584199901005

theorem tailTrace_4307863 : CollatzResearch.WordTrace tailWord_4307863 prefixEnd_4307863 2212004312719584199901005 := by
  unfold tailWord_4307863
  simp only [CollatzResearch.WordTrace]
  refine ⟨157120671592355550271496243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104747114394903700180997495 157120671592355550271496243)
  ·
    refine ⟨235681007388533325407244365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157120671592355550271496243 235681007388533325407244365)
    ·
      refine ⟨88380377770699997027716637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235681007388533325407244365 88380377770699997027716637)
      ·
        refine ⟨33142641664012498885393739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88380377770699997027716637 33142641664012498885393739)
        ·
          refine ⟨49713962496018748328090609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33142641664012498885393739 49713962496018748328090609)
          ·
            refine ⟨37285471872014061246067957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49713962496018748328090609 37285471872014061246067957)
            ·
              refine ⟨3495512988001318241818871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37285471872014061246067957 3495512988001318241818871)
              ·
                refine ⟨5243269482001977362728307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495512988001318241818871 5243269482001977362728307)
                ·
                  refine ⟨7864904223002966044092461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243269482001977362728307 7864904223002966044092461)
                  ·
                    refine ⟨2949339083626112266534673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7864904223002966044092461 2949339083626112266534673)
                    ·
                      refine ⟨2212004312719584199901005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949339083626112266534673 2212004312719584199901005)
                      ·
                        rfl

theorem cell23_4307863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_4307863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307863 prefixEnd_4307863 := by exact prefixLift 4307863
  have htrace : WordTrace (prefixWord ++ tailWord_4307863) baseStart_4307863 baseEnd_4307863 := by
    simpa [prefixWord, tailWord_4307863, baseEnd_4307863] using wordTrace_append hprefix tailTrace_4307863
  have hstable : (prefixWord ++ tailWord_4307863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307863).length < 2 ^ (prefixWord ++ tailWord_4307863).sum := by decide
  have hdescent : baseEnd_4307863 < baseStart_4307863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307893 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_4307893 : Nat := 118140960795 + 4307893 * 2 ^ 59
def prefixEnd_4307893 : Nat := 4983230072969 + 3 ^ 40 * 4307893 * 2
def baseEnd_4307893 : Nat := 2212019717139219082525867

theorem tailTrace_4307893 : CollatzResearch.WordTrace tailWord_4307893 prefixEnd_4307893 2212019717139219082525867 := by
  unfold tailWord_4307893
  simp only [CollatzResearch.WordTrace]
  refine ⟨157121765782246865395088333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104747843854831243596725555 157121765782246865395088333)
  ·
    refine ⟨58920662168342574523158125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157121765782246865395088333 58920662168342574523158125)
    ·
      refine ⟨22095248313128465446184297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58920662168342574523158125 22095248313128465446184297)
      ·
        refine ⟨16571436234846349084638223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22095248313128465446184297 16571436234846349084638223)
        ·
          refine ⟨24857154352269523626957335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16571436234846349084638223 24857154352269523626957335)
          ·
            refine ⟨37285731528404285440436003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24857154352269523626957335 37285731528404285440436003)
            ·
              refine ⟨55928597292606428160654005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37285731528404285440436003 55928597292606428160654005)
              ·
                refine ⟨5243305996181852640061313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55928597292606428160654005 5243305996181852640061313)
                ·
                  refine ⟨3932479497136389480045985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243305996181852640061313 3932479497136389480045985)
                  ·
                    refine ⟨2949359622852292110034489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932479497136389480045985 2949359622852292110034489)
                    ·
                      refine ⟨2212019717139219082525867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949359622852292110034489 2212019717139219082525867)
                      ·
                        rfl

theorem cell23_4307893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_4307893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307893 prefixEnd_4307893 := by exact prefixLift 4307893
  have htrace : WordTrace (prefixWord ++ tailWord_4307893) baseStart_4307893 baseEnd_4307893 := by
    simpa [prefixWord, tailWord_4307893, baseEnd_4307893] using wordTrace_append hprefix tailTrace_4307893
  have hstable : (prefixWord ++ tailWord_4307893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307893).length < 2 ^ (prefixWord ++ tailWord_4307893).sum := by decide
  have hdescent : baseEnd_4307893 < baseStart_4307893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307916 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 5]
def baseStart_4307916 : Nat := 118140960795 + 4307916 * 2 ^ 59
def prefixEnd_4307916 : Nat := 4983230072969 + 3 ^ 40 * 4307916 * 2
def baseEnd_4307916 : Nat := 245781280799363610282029

theorem tailTrace_4307916 : CollatzResearch.WordTrace tailWord_4307916 prefixEnd_4307916 245781280799363610282029 := by
  unfold tailWord_4307916
  simp only [CollatzResearch.WordTrace]
  refine ⟨78561302330581770161587801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104748403107442360215450401 78561302330581770161587801)
  ·
    refine ⟨58920976747936327621190851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78561302330581770161587801 58920976747936327621190851)
    ·
      refine ⟨88381465121904491431786277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58920976747936327621190851 88381465121904491431786277)
      ·
        refine ⟨16571524710357092143459927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88381465121904491431786277 16571524710357092143459927)
        ·
          refine ⟨24857287065535638215189891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16571524710357092143459927 24857287065535638215189891)
          ·
            refine ⟨37285930598303457322784837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24857287065535638215189891 37285930598303457322784837)
            ·
              refine ⟨6991111987181898248022157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37285930598303457322784837 6991111987181898248022157)
              ·
                refine ⟨2621666995193211843008309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6991111987181898248022157 2621666995193211843008309)
                ·
                  refine ⟨245781280799363610282029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621666995193211843008309 245781280799363610282029)
                  ·
                    rfl

theorem cell23_4307916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_4307916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307916 prefixEnd_4307916 := by exact prefixLift 4307916
  have htrace : WordTrace (prefixWord ++ tailWord_4307916) baseStart_4307916 baseEnd_4307916 := by
    simpa [prefixWord, tailWord_4307916, baseEnd_4307916] using wordTrace_append hprefix tailTrace_4307916
  have hstable : (prefixWord ++ tailWord_4307916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307916).length < 2 ^ (prefixWord ++ tailWord_4307916).sum := by decide
  have hdescent : baseEnd_4307916 < baseStart_4307916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4307989 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 8]
def baseStart_4307989 : Nat := 118140960795 + 4307989 * 2 ^ 59
def prefixEnd_4307989 : Nat := 4983230072969 + 3 ^ 40 * 4307989 * 2
def baseEnd_4307989 : Nat := 245785445698005634102825

theorem tailTrace_4307989 : CollatzResearch.WordTrace tailWord_4307989 prefixEnd_4307989 245785445698005634102825 := by
  unfold tailWord_4307989
  simp only [CollatzResearch.WordTrace]
  refine ⟨157125267189899073790583021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104750178126599382527055347 157125267189899073790583021)
  ·
    refine ⟨58921975196212152671468633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157125267189899073790583021 58921975196212152671468633)
    ·
      refine ⟨44191481397159114503601475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58921975196212152671468633 44191481397159114503601475)
      ·
        refine ⟨66287222095738671755402213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44191481397159114503601475 66287222095738671755402213)
        ·
          refine ⟨12428854142951000954137915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66287222095738671755402213 12428854142951000954137915)
          ·
            refine ⟨18643281214426501431206873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12428854142951000954137915 18643281214426501431206873)
            ·
              refine ⟨13982460910819876073405155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18643281214426501431206873 13982460910819876073405155)
              ·
                refine ⟨20973691366229814110107733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13982460910819876073405155 20973691366229814110107733)
                ·
                  refine ⟨245785445698005634102825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20973691366229814110107733 245785445698005634102825)
                  ·
                    rfl

theorem cell23_4307989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_4307989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4307989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4307989 prefixEnd_4307989 := by exact prefixLift 4307989
  have htrace : WordTrace (prefixWord ++ tailWord_4307989) baseStart_4307989 baseEnd_4307989 := by
    simpa [prefixWord, tailWord_4307989, baseEnd_4307989] using wordTrace_append hprefix tailTrace_4307989
  have hstable : (prefixWord ++ tailWord_4307989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4307989).length < 2 ^ (prefixWord ++ tailWord_4307989).sum := by decide
  have hdescent : baseEnd_4307989 < baseStart_4307989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4307989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308016 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3]
def baseStart_4308016 : Nat := 118140960795 + 4308016 * 2 ^ 59
def prefixEnd_4308016 : Nat := 4983230072969 + 3 ^ 40 * 4308016 * 2
def baseEnd_4308016 : Nat := 2212082875259722101287801

theorem tailTrace_4308016 : CollatzResearch.WordTrace tailWord_4308016 prefixEnd_4308016 2212082875259722101287801 := by
  unfold tailWord_4308016
  simp only [CollatzResearch.WordTrace]
  refine ⟨78563125980400628700907951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104750834640534171601210601 78563125980400628700907951)
  ·
    refine ⟨117844688970600943051361927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78563125980400628700907951 117844688970600943051361927)
    ·
      refine ⟨176767033455901414577042891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117844688970600943051361927 176767033455901414577042891)
      ·
        refine ⟨265150550183852121865564337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176767033455901414577042891 265150550183852121865564337)
        ·
          refine ⟨198862912637889091399173253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265150550183852121865564337 198862912637889091399173253)
          ·
            refine ⟨37286796119604204637344985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198862912637889091399173253 37286796119604204637344985)
            ·
              refine ⟨27965097089703153478008739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37286796119604204637344985 27965097089703153478008739)
              ·
                refine ⟨41947645634554730217013109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27965097089703153478008739 41947645634554730217013109)
                ·
                  refine ⟨3932591778239505957844979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41947645634554730217013109 3932591778239505957844979)
                  ·
                    refine ⟨5898887667359258936767469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932591778239505957844979 5898887667359258936767469)
                    ·
                      refine ⟨2212082875259722101287801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898887667359258936767469 2212082875259722101287801)
                      ·
                        rfl

theorem cell23_4308016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_4308016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308016 prefixEnd_4308016 := by exact prefixLift 4308016
  have htrace : WordTrace (prefixWord ++ tailWord_4308016) baseStart_4308016 baseEnd_4308016 := by
    simpa [prefixWord, tailWord_4308016, baseEnd_4308016] using wordTrace_append hprefix tailTrace_4308016
  have hstable : (prefixWord ++ tailWord_4308016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308016).length < 2 ^ (prefixWord ++ tailWord_4308016).sum := by decide
  have hdescent : baseEnd_4308016 < baseStart_4308016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308020 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4308020 : Nat := 118140960795 + 4308020 * 2 ^ 59
def prefixEnd_4308020 : Nat := 4983230072969 + 3 ^ 40 * 4308020 * 2
def baseEnd_4308020 : Nat := 2212084929182340085637783

theorem tailTrace_4308020 : CollatzResearch.WordTrace tailWord_4308020 prefixEnd_4308020 2212084929182340085637783 := by
  unfold tailWord_4308020
  simp only [CollatzResearch.WordTrace]
  refine ⟨78563198926393383042480757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104750931901857844056641009 78563198926393383042480757)
  ·
    refine ⟨7365299899349379660232571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78563198926393383042480757 7365299899349379660232571)
    ·
      refine ⟨11047949849024069490348857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7365299899349379660232571 11047949849024069490348857)
      ·
        refine ⟨8285962386768052117761643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11047949849024069490348857 8285962386768052117761643)
        ·
          refine ⟨12428943580152078176642465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285962386768052117761643 12428943580152078176642465)
          ·
            refine ⟨9321707685114058632481849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12428943580152078176642465 9321707685114058632481849)
            ·
              refine ⟨6991280763835543974361387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9321707685114058632481849 6991280763835543974361387)
              ·
                refine ⟨10486921145753315961542081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6991280763835543974361387 10486921145753315961542081)
                ·
                  refine ⟨7865190859314986971156561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10486921145753315961542081 7865190859314986971156561)
                  ·
                    refine ⟨5898893144486240228367421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7865190859314986971156561 5898893144486240228367421)
                    ·
                      refine ⟨2212084929182340085637783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898893144486240228367421 2212084929182340085637783)
                      ·
                        rfl

theorem cell23_4308020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4308020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308020 prefixEnd_4308020 := by exact prefixLift 4308020
  have htrace : WordTrace (prefixWord ++ tailWord_4308020) baseStart_4308020 baseEnd_4308020 := by
    simpa [prefixWord, tailWord_4308020, baseEnd_4308020] using wordTrace_append hprefix tailTrace_4308020
  have hstable : (prefixWord ++ tailWord_4308020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308020).length < 2 ^ (prefixWord ++ tailWord_4308020).sum := by decide
  have hdescent : baseEnd_4308020 < baseStart_4308020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308026 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_4308026 : Nat := 118140960795 + 4308026 * 2 ^ 59
def prefixEnd_4308026 : Nat := 4983230072969 + 3 ^ 40 * 4308026 * 2
def baseEnd_4308026 : Nat := 2212088010066267062162755

theorem tailTrace_4308026 : CollatzResearch.WordTrace tailWord_4308026 prefixEnd_4308026 2212088010066267062162755 := by
  unfold tailWord_4308026
  simp only [CollatzResearch.WordTrace]
  refine ⟨39281654172691257277419983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104751077793843352739786621 39281654172691257277419983)
  ·
    refine ⟨58922481259036885916129975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39281654172691257277419983 58922481259036885916129975)
    ·
      refine ⟨88383721888555328874194963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58922481259036885916129975 88383721888555328874194963)
      ·
        refine ⟨132575582832832993311292445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88383721888555328874194963 132575582832832993311292445)
        ·
          refine ⟨49715843562312372491734667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132575582832832993311292445 49715843562312372491734667)
          ·
            refine ⟨74573765343468558737602001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49715843562312372491734667 74573765343468558737602001)
            ·
              refine ⟨55930324007601419053201501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74573765343468558737602001 55930324007601419053201501)
              ·
                refine ⟨20973871502850532144950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55930324007601419053201501 20973871502850532144950563)
                ·
                  refine ⟨31460807254275798217425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20973871502850532144950563 31460807254275798217425845)
                  ·
                    refine ⟨2949450680088356082883673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31460807254275798217425845 2949450680088356082883673)
                    ·
                      refine ⟨2212088010066267062162755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949450680088356082883673 2212088010066267062162755)
                      ·
                        rfl

theorem cell23_4308026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_4308026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308026 prefixEnd_4308026 := by exact prefixLift 4308026
  have htrace : WordTrace (prefixWord ++ tailWord_4308026) baseStart_4308026 baseEnd_4308026 := by
    simpa [prefixWord, tailWord_4308026, baseEnd_4308026] using wordTrace_append hprefix tailTrace_4308026
  have hstable : (prefixWord ++ tailWord_4308026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308026).length < 2 ^ (prefixWord ++ tailWord_4308026).sum := by decide
  have hdescent : baseEnd_4308026 < baseStart_4308026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308073 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 5, 2, 2]
def baseStart_4308073 : Nat := 118140960795 + 4308073 * 2 ^ 59
def prefixEnd_4308073 : Nat := 4983230072969 + 3 ^ 40 * 4308073 * 2
def baseEnd_4308073 : Nat := 2212112143657028378275039

theorem tailTrace_4308073 : CollatzResearch.WordTrace tailWord_4308073 prefixEnd_4308073 2212112143657028378275039 := by
  unfold tailWord_4308073
  simp only [CollatzResearch.WordTrace]
  refine ⟨157128330921594756136640873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104752220614396504091093915 157128330921594756136640873)
  ·
    refine ⟨117846248191196067102480655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157128330921594756136640873 117846248191196067102480655)
    ·
      refine ⟨176769372286794100653720983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117846248191196067102480655 176769372286794100653720983)
      ·
        refine ⟨265154058430191150980581475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176769372286794100653720983 265154058430191150980581475)
        ·
          refine ⟨397731087645286726470872213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265154058430191150980581475 397731087645286726470872213)
          ·
            refine ⟨18643644733372815303322135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 397731087645286726470872213 18643644733372815303322135)
            ·
              refine ⟨27965467100059222954983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18643644733372815303322135 27965467100059222954983203)
              ·
                refine ⟨41948200650088834432474805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27965467100059222954983203 41948200650088834432474805)
                ·
                  refine ⟨3932643810945828228044513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41948200650088834432474805 3932643810945828228044513)
                  ·
                    refine ⟨2949482858209371171033385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932643810945828228044513 2949482858209371171033385)
                    ·
                      refine ⟨2212112143657028378275039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949482858209371171033385 2212112143657028378275039)
                      ·
                        rfl

theorem cell23_4308073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 2, 2].length) (baseStart_4308073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308073 prefixEnd_4308073 := by exact prefixLift 4308073
  have htrace : WordTrace (prefixWord ++ tailWord_4308073) baseStart_4308073 baseEnd_4308073 := by
    simpa [prefixWord, tailWord_4308073, baseEnd_4308073] using wordTrace_append hprefix tailTrace_4308073
  have hstable : (prefixWord ++ tailWord_4308073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308073).length < 2 ^ (prefixWord ++ tailWord_4308073).sum := by decide
  have hdescent : baseEnd_4308073 < baseStart_4308073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308076 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_4308076 : Nat := 118140960795 + 4308076 * 2 ^ 59
def prefixEnd_4308076 : Nat := 4983230072969 + 3 ^ 40 * 4308076 * 2
def baseEnd_4308076 : Nat := 2212113684098991866537525

theorem tailTrace_4308076 : CollatzResearch.WordTrace tailWord_4308076 prefixEnd_4308076 2212113684098991866537525 := by
  unfold tailWord_4308076
  simp only [CollatzResearch.WordTrace]
  refine ⟨78564220170291943824500041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104752293560389258432666721 78564220170291943824500041)
  ·
    refine ⟨58923165127718957868375031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78564220170291943824500041 58923165127718957868375031)
    ·
      refine ⟨88384747691578436802562547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58923165127718957868375031 88384747691578436802562547)
      ·
        refine ⟨132577121537367655203843821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88384747691578436802562547 132577121537367655203843821)
        ·
          refine ⟨49716420576512870701441433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132577121537367655203843821 49716420576512870701441433)
          ·
            refine ⟨37287315432384653026081075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49716420576512870701441433 37287315432384653026081075)
            ·
              refine ⟨55930973148576979539121613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37287315432384653026081075 55930973148576979539121613)
              ·
                refine ⟨20974114930716367327170605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55930973148576979539121613 20974114930716367327170605)
                ·
                  refine ⟨7865293099018637747688977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20974114930716367327170605 7865293099018637747688977)
                  ·
                    refine ⟨5898969824263978310766733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7865293099018637747688977 5898969824263978310766733)
                    ·
                      refine ⟨2212113684098991866537525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898969824263978310766733 2212113684098991866537525)
                      ·
                        rfl

theorem cell23_4308076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_4308076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308076 prefixEnd_4308076 := by exact prefixLift 4308076
  have htrace : WordTrace (prefixWord ++ tailWord_4308076) baseStart_4308076 baseEnd_4308076 := by
    simpa [prefixWord, tailWord_4308076, baseEnd_4308076] using wordTrace_append hprefix tailTrace_4308076
  have hstable : (prefixWord ++ tailWord_4308076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308076).length < 2 ^ (prefixWord ++ tailWord_4308076).sum := by decide
  have hdescent : baseEnd_4308076 < baseStart_4308076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308093 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_4308093 : Nat := 118140960795 + 4308093 * 2 ^ 59
def prefixEnd_4308093 : Nat := 4983230072969 + 3 ^ 40 * 4308093 * 2
def baseEnd_4308093 : Nat := 2212122413270118300024947

theorem tailTrace_4308093 : CollatzResearch.WordTrace tailWord_4308093 prefixEnd_4308093 2212122413270118300024947 := by
  unfold tailWord_4308093
  simp only [CollatzResearch.WordTrace]
  refine ⟨157129060381522299552368933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104752706921014866368245955 157129060381522299552368933)
  ·
    refine ⟨29461698821535431166069175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157129060381522299552368933 29461698821535431166069175)
    ·
      refine ⟨44192548232303146749103763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29461698821535431166069175 44192548232303146749103763)
      ·
        refine ⟨66288822348454720123655645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44192548232303146749103763 66288822348454720123655645)
        ·
          refine ⟨24858308380670520046370867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66288822348454720123655645 24858308380670520046370867)
          ·
            refine ⟨37287462571005780069556301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24858308380670520046370867 37287462571005780069556301)
            ·
              refine ⟨13982798464127167526083613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37287462571005780069556301 13982798464127167526083613)
              ·
                refine ⟨5243549424047687822281355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13982798464127167526083613 5243549424047687822281355)
                ·
                  refine ⟨7865324136071531733422033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243549424047687822281355 7865324136071531733422033)
                  ·
                    refine ⟨5898993102053648800066525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7865324136071531733422033 5898993102053648800066525)
                    ·
                      refine ⟨2212122413270118300024947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5898993102053648800066525 2212122413270118300024947)
                      ·
                        rfl

theorem cell23_4308093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_4308093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308093 prefixEnd_4308093 := by exact prefixLift 4308093
  have htrace : WordTrace (prefixWord ++ tailWord_4308093) baseStart_4308093 baseEnd_4308093 := by
    simpa [prefixWord, tailWord_4308093, baseEnd_4308093] using wordTrace_append hprefix tailTrace_4308093
  have hstable : (prefixWord ++ tailWord_4308093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308093).length < 2 ^ (prefixWord ++ tailWord_4308093).sum := by decide
  have hdescent : baseEnd_4308093 < baseStart_4308093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308100 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_4308100 : Nat := 118140960795 + 4308100 * 2 ^ 59
def prefixEnd_4308100 : Nat := 4983230072969 + 3 ^ 40 * 4308100 * 2
def baseEnd_4308100 : Nat := 737375335878233257545805

theorem tailTrace_4308100 : CollatzResearch.WordTrace tailWord_4308100 prefixEnd_4308100 737375335878233257545805 := by
  unfold tailWord_4308100
  simp only [CollatzResearch.WordTrace]
  refine ⟨78564657846248469873936877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104752877128331293165249169 78564657846248469873936877)
  ·
    refine ⟨29461746692343176202726329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78564657846248469873936877 29461746692343176202726329)
    ·
      refine ⟨22096310019257382152044747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29461746692343176202726329 22096310019257382152044747)
      ·
        refine ⟨33144465028886073228067121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22096310019257382152044747 33144465028886073228067121)
        ·
          refine ⟨24858348771664554921050341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33144465028886073228067121 24858348771664554921050341)
          ·
            refine ⟨4660940394687104047696939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24858348771664554921050341 4660940394687104047696939)
            ·
              refine ⟨6991410592030656071545409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660940394687104047696939 6991410592030656071545409)
              ·
                refine ⟨5243557944022992053659057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6991410592030656071545409 5243557944022992053659057)
                ·
                  refine ⟨3932668458017244040244293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243557944022992053659057 3932668458017244040244293)
                  ·
                    refine ⟨737375335878233257545805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3932668458017244040244293 737375335878233257545805)
                    ·
                      rfl

theorem cell23_4308100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_4308100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308100 prefixEnd_4308100 := by exact prefixLift 4308100
  have htrace : WordTrace (prefixWord ++ tailWord_4308100) baseStart_4308100 baseEnd_4308100 := by
    simpa [prefixWord, tailWord_4308100, baseEnd_4308100] using wordTrace_append hprefix tailTrace_4308100
  have hstable : (prefixWord ++ tailWord_4308100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308100).length < 2 ^ (prefixWord ++ tailWord_4308100).sum := by decide
  have hdescent : baseEnd_4308100 < baseStart_4308100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308130 : List Nat := [3, 3, 1, 3, 2, 2, 2, 7]
def baseStart_4308130 : Nat := 118140960795 + 4308130 * 2 ^ 59
def prefixEnd_4308130 : Nat := 4983230072969 + 3 ^ 40 * 4308130 * 2
def baseEnd_4308130 : Nat := 81931163409419802046751

theorem tailTrace_4308130 : CollatzResearch.WordTrace tailWord_4308130 prefixEnd_4308130 81931163409419802046751 := by
  unfold tailWord_4308130
  simp only [CollatzResearch.WordTrace]
  refine ⟨39282602470597063717866461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104753606588258836580977229 39282602470597063717866461)
  ·
    refine ⟨14730975926473898894199923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39282602470597063717866461 14730975926473898894199923)
    ·
      refine ⟨22096463889710848341299885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14730975926473898894199923 22096463889710848341299885)
      ·
        refine ⟨8286173958641568127987457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22096463889710848341299885 8286173958641568127987457)
        ·
          refine ⟨6214630468981176095990593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8286173958641568127987457 6214630468981176095990593)
          ·
            refine ⟨4660972851735882071992945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6214630468981176095990593 4660972851735882071992945)
            ·
              refine ⟨3495729638801911553994709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4660972851735882071992945 3495729638801911553994709)
              ·
                refine ⟨81931163409419802046751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3495729638801911553994709 81931163409419802046751)
                ·
                  rfl

theorem cell23_4308130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_4308130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308130 prefixEnd_4308130 := by exact prefixLift 4308130
  have htrace : WordTrace (prefixWord ++ tailWord_4308130) baseStart_4308130 baseEnd_4308130 := by
    simpa [prefixWord, tailWord_4308130, baseEnd_4308130] using wordTrace_append hprefix tailTrace_4308130
  have hstable : (prefixWord ++ tailWord_4308130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308130).length < 2 ^ (prefixWord ++ tailWord_4308130).sum := by decide
  have hdescent : baseEnd_4308130 < baseStart_4308130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308141 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_4308141 : Nat := 118140960795 + 4308141 * 2 ^ 59
def prefixEnd_4308141 : Nat := 4983230072969 + 3 ^ 40 * 4308141 * 2
def baseEnd_4308141 : Nat := 2212147060341534112224727

theorem tailTrace_4308141 : CollatzResearch.WordTrace tailWord_4308141 prefixEnd_4308141 2212147060341534112224727 := by
  unfold tailWord_4308141
  simp only [CollatzResearch.WordTrace]
  refine ⟨157130811085348403750116277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104753874056898935833410851 157130811085348403750116277)
  ·
    refine ⟨14731013539251412851573401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157130811085348403750116277 14731013539251412851573401)
    ·
      refine ⟨11048260154438559638680051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14731013539251412851573401 11048260154438559638680051)
      ·
        refine ⟨16572390231657839458020077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11048260154438559638680051 16572390231657839458020077)
        ·
          refine ⟨6214646336871689796757529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16572390231657839458020077 6214646336871689796757529)
          ·
            refine ⟨4660984752653767347568147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6214646336871689796757529 4660984752653767347568147)
            ·
              refine ⟨6991477128980651021352221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660984752653767347568147 6991477128980651021352221)
              ·
                refine ⟨2621803923367744133007083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6991477128980651021352221 2621803923367744133007083)
                ·
                  refine ⟨3932705885051616199510625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621803923367744133007083 3932705885051616199510625)
                  ·
                    refine ⟨2949529413788712149632969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932705885051616199510625 2949529413788712149632969)
                    ·
                      refine ⟨2212147060341534112224727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949529413788712149632969 2212147060341534112224727)
                      ·
                        rfl

theorem cell23_4308141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_4308141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308141 prefixEnd_4308141 := by exact prefixLift 4308141
  have htrace : WordTrace (prefixWord ++ tailWord_4308141) baseStart_4308141 baseEnd_4308141 := by
    simpa [prefixWord, tailWord_4308141, baseEnd_4308141] using wordTrace_append hprefix tailTrace_4308141
  have hstable : (prefixWord ++ tailWord_4308141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308141).length < 2 ^ (prefixWord ++ tailWord_4308141).sum := by decide
  have hdescent : baseEnd_4308141 < baseStart_4308141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308174 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_4308174 : Nat := 118140960795 + 4308174 * 2 ^ 59
def prefixEnd_4308174 : Nat := 4983230072969 + 3 ^ 40 * 4308174 * 2
def baseEnd_4308174 : Nat := 2212164005203132483112075

theorem tailTrace_4308174 : CollatzResearch.WordTrace tailWord_4308174 prefixEnd_4308174 2212164005203132483112075 := by
  unfold tailWord_4308174
  simp only [CollatzResearch.WordTrace]
  refine ⟨19641501836778606298258447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104754676462819233590711717 19641501836778606298258447)
  ·
    refine ⟨29462252755167909447387671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19641501836778606298258447 29462252755167909447387671)
    ·
      refine ⟨44193379132751864171081507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29462252755167909447387671 44193379132751864171081507)
      ·
        refine ⟨66290068699127796256622261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44193379132751864171081507 66290068699127796256622261)
        ·
          refine ⟨6214693940543230899058337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66290068699127796256622261 6214693940543230899058337)
          ·
            refine ⟨4661020455407423174293753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6214693940543230899058337 4661020455407423174293753)
            ·
              refine ⟨3495765341555567380720315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4661020455407423174293753 3495765341555567380720315)
              ·
                refine ⟨5243648012333351071080473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495765341555567380720315 5243648012333351071080473)
                ·
                  refine ⟨3932736009250013303310355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243648012333351071080473 3932736009250013303310355)
                  ·
                    refine ⟨5899104013875019954965533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932736009250013303310355 5899104013875019954965533)
                    ·
                      refine ⟨2212164005203132483112075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899104013875019954965533 2212164005203132483112075)
                      ·
                        rfl

theorem cell23_4308174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_4308174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308174 prefixEnd_4308174 := by exact prefixLift 4308174
  have htrace : WordTrace (prefixWord ++ tailWord_4308174) baseStart_4308174 baseEnd_4308174 := by
    simpa [prefixWord, tailWord_4308174, baseEnd_4308174] using wordTrace_append hprefix tailTrace_4308174
  have hstable : (prefixWord ++ tailWord_4308174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308174).length < 2 ^ (prefixWord ++ tailWord_4308174).sum := by decide
  have hdescent : baseEnd_4308174 < baseStart_4308174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308179 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_4308179 : Nat := 118140960795 + 4308179 * 2 ^ 59
def prefixEnd_4308179 : Nat := 4983230072969 + 3 ^ 40 * 4308179 * 2
def baseEnd_4308179 : Nat := 2212166572606404963549551

theorem tailTrace_4308179 : CollatzResearch.WordTrace tailWord_4308179 prefixEnd_4308179 2212166572606404963549551 := by
  unfold tailWord_4308179
  simp only [CollatzResearch.WordTrace]
  refine ⟨157132197059210736239999591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104754798039473824159999727 157132197059210736239999591)
  ·
    refine ⟨235698295588816104359999387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157132197059210736239999591 235698295588816104359999387)
    ·
      refine ⟨353547443383224156539999081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235698295588816104359999387 353547443383224156539999081)
      ·
        refine ⟨265160582537418117404999311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353547443383224156539999081 265160582537418117404999311)
        ·
          refine ⟨397740873806127176107498967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265160582537418117404999311 397740873806127176107498967)
          ·
            refine ⟨596611310709190764161248451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397740873806127176107498967 596611310709190764161248451)
            ·
              refine ⟨894916966063786146241872677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596611310709190764161248451 894916966063786146241872677)
              ·
                refine ⟨167796931136959902420351127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 894916966063786146241872677 167796931136959902420351127)
                ·
                  refine ⟨251695396705439853630526691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167796931136959902420351127 251695396705439853630526691)
                  ·
                    refine ⟨377543095058159780445790037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251695396705439853630526691 377543095058159780445790037)
                    ·
                      refine ⟨2212166572606404963549551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 377543095058159780445790037 2212166572606404963549551)
                      ·
                        rfl

theorem cell23_4308179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_4308179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308179 prefixEnd_4308179 := by exact prefixLift 4308179
  have htrace : WordTrace (prefixWord ++ tailWord_4308179) baseStart_4308179 baseEnd_4308179 := by
    simpa [prefixWord, tailWord_4308179, baseEnd_4308179] using wordTrace_append hprefix tailTrace_4308179
  have hstable : (prefixWord ++ tailWord_4308179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308179).length < 2 ^ (prefixWord ++ tailWord_4308179).sum := by decide
  have hdescent : baseEnd_4308179 < baseStart_4308179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308184 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_4308184 : Nat := 118140960795 + 4308184 * 2 ^ 59
def prefixEnd_4308184 : Nat := 4983230072969 + 3 ^ 40 * 4308184 * 2
def baseEnd_4308184 : Nat := 2212169140009677443987029

theorem tailTrace_4308184 : CollatzResearch.WordTrace tailWord_4308184 prefixEnd_4308184 2212169140009677443987029 := by
  unfold tailWord_4308184
  simp only [CollatzResearch.WordTrace]
  refine ⟨78566189712096311046965803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104754919616128414729287737 78566189712096311046965803)
  ·
    refine ⟨117849284568144466570448705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78566189712096311046965803 117849284568144466570448705)
    ·
      refine ⟨88386963426108349927836529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117849284568144466570448705 88386963426108349927836529)
      ·
        refine ⟨66290222569581262445877397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88386963426108349927836529 66290222569581262445877397)
        ·
          refine ⟨3107354182949121677150503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66290222569581262445877397 3107354182949121677150503)
          ·
            refine ⟨4661031274423682515725755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107354182949121677150503 4661031274423682515725755)
            ·
              refine ⟨6991546911635523773588633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661031274423682515725755 6991546911635523773588633)
              ·
                refine ⟨5243660183726642830191475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6991546911635523773588633 5243660183726642830191475)
                ·
                  refine ⟨7865490275589964245287213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243660183726642830191475 7865490275589964245287213)
                  ·
                    refine ⟨2949558853346236591982705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7865490275589964245287213 2949558853346236591982705)
                    ·
                      refine ⟨2212169140009677443987029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949558853346236591982705 2212169140009677443987029)
                      ·
                        rfl

theorem cell23_4308184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_4308184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308184 prefixEnd_4308184 := by exact prefixLift 4308184
  have htrace : WordTrace (prefixWord ++ tailWord_4308184) baseStart_4308184 baseEnd_4308184 := by
    simpa [prefixWord, tailWord_4308184, baseEnd_4308184] using wordTrace_append hprefix tailTrace_4308184
  have hstable : (prefixWord ++ tailWord_4308184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308184).length < 2 ^ (prefixWord ++ tailWord_4308184).sum := by decide
  have hdescent : baseEnd_4308184 < baseStart_4308184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308220 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 5]
def baseStart_4308220 : Nat := 118140960795 + 4308220 * 2 ^ 59
def prefixEnd_4308220 : Nat := 4983230072969 + 3 ^ 40 * 4308220 * 2
def baseEnd_4308220 : Nat := 245798625034804367015207

theorem tailTrace_4308220 : CollatzResearch.WordTrace tailWord_4308220 prefixEnd_4308220 245798625034804367015207 := by
  unfold tailWord_4308220
  simp only [CollatzResearch.WordTrace]
  refine ⟨78566846226031100121121057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104755794968041466828161409 78566846226031100121121057)
  ·
    refine ⟨58925134669523325090840793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78566846226031100121121057 58925134669523325090840793)
    ·
      refine ⟨44193851002142493818130595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58925134669523325090840793 44193851002142493818130595)
      ·
        refine ⟨66290776503213740727195893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44193851002142493818130595 66290776503213740727195893)
        ·
          refine ⟨6214760297176288193174615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66290776503213740727195893 6214760297176288193174615)
          ·
            refine ⟨9322140445764432289761923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6214760297176288193174615 9322140445764432289761923)
            ·
              refine ⟨13983210668646648434642885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322140445764432289761923 13983210668646648434642885)
              ·
                refine ⟨2621852000371246581495541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13983210668646648434642885 2621852000371246581495541)
                ·
                  refine ⟨245798625034804367015207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621852000371246581495541 245798625034804367015207)
                  ·
                    rfl

theorem cell23_4308220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_4308220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308220 prefixEnd_4308220 := by exact prefixLift 4308220
  have htrace : WordTrace (prefixWord ++ tailWord_4308220) baseStart_4308220 baseEnd_4308220 := by
    simpa [prefixWord, tailWord_4308220, baseEnd_4308220] using wordTrace_append hprefix tailTrace_4308220
  have hstable : (prefixWord ++ tailWord_4308220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308220).length < 2 ^ (prefixWord ++ tailWord_4308220).sum := by decide
  have hdescent : baseEnd_4308220 < baseStart_4308220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308223 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 5, 2]
def baseStart_4308223 : Nat := 118140960795 + 4308223 * 2 ^ 59
def prefixEnd_4308223 : Nat := 4983230072969 + 3 ^ 40 * 4308223 * 2
def baseEnd_4308223 : Nat := 2212189165755202791399349

theorem tailTrace_4308223 : CollatzResearch.WordTrace tailWord_4308223 prefixEnd_4308223 2212189165755202791399349 := by
  unfold tailWord_4308223
  simp only [CollatzResearch.WordTrace]
  refine ⟨157133801871051331754601323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104755867914034221169734215 157133801871051331754601323)
  ·
    refine ⟨235700702806576997631901985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157133801871051331754601323 235700702806576997631901985)
    ·
      refine ⟨176775527104932748223926489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235700702806576997631901985 176775527104932748223926489)
      ·
        refine ⟨132581645328699561167944867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176775527104932748223926489 132581645328699561167944867)
        ·
          refine ⟨198872467993049341751917301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132581645328699561167944867 198872467993049341751917301)
          ·
            refine ⟨18644293874348375789242247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198872467993049341751917301 18644293874348375789242247)
            ·
              refine ⟨27966440811522563683863371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18644293874348375789242247 27966440811522563683863371)
              ·
                refine ⟨41949661217283845525795057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27966440811522563683863371 41949661217283845525795057)
                ·
                  refine ⟨31462245912962884144346293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41949661217283845525795057 31462245912962884144346293)
                  ·
                    refine ⟨2949585554340270388532465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31462245912962884144346293 2949585554340270388532465)
                    ·
                      refine ⟨2212189165755202791399349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949585554340270388532465 2212189165755202791399349)
                      ·
                        rfl

theorem cell23_4308223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_4308223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308223 prefixEnd_4308223 := by exact prefixLift 4308223
  have htrace : WordTrace (prefixWord ++ tailWord_4308223) baseStart_4308223 baseEnd_4308223 := by
    simpa [prefixWord, tailWord_4308223, baseEnd_4308223] using wordTrace_append hprefix tailTrace_4308223
  have hstable : (prefixWord ++ tailWord_4308223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308223).length < 2 ^ (prefixWord ++ tailWord_4308223).sum := by decide
  have hdescent : baseEnd_4308223 < baseStart_4308223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308250 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_4308250 : Nat := 118140960795 + 4308250 * 2 ^ 59
def prefixEnd_4308250 : Nat := 4983230072969 + 3 ^ 40 * 4308250 * 2
def baseEnd_4308250 : Nat := 737401009910958061920575

theorem tailTrace_4308250 : CollatzResearch.WordTrace tailWord_4308250 prefixEnd_4308250 737401009910958061920575 := by
  unfold tailWord_4308250
  simp only [CollatzResearch.WordTrace]
  refine ⟨39283696660488378841458551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104756524427969010243889469 39283696660488378841458551)
  ·
    refine ⟨58925544990732568262187827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39283696660488378841458551 58925544990732568262187827)
    ·
      refine ⟨88388317486098852393281741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58925544990732568262187827 88388317486098852393281741)
      ·
        refine ⟨33145619057287069647480653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88388317486098852393281741 33145619057287069647480653)
        ·
          refine ⟨12429607146482651117805245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33145619057287069647480653 12429607146482651117805245)
          ·
            refine ⟨4661102679930994169176967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12429607146482651117805245 4661102679930994169176967)
            ·
              refine ⟨6991654019896491253765451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661102679930994169176967 6991654019896491253765451)
              ·
                refine ⟨10487481029844736880648177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6991654019896491253765451 10487481029844736880648177)
                ·
                  refine ⟨7865610772383552660486133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10487481029844736880648177 7865610772383552660486133)
                  ·
                    refine ⟨737401009910958061920575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7865610772383552660486133 737401009910958061920575)
                    ·
                      rfl

theorem cell23_4308250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_4308250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308250 prefixEnd_4308250 := by exact prefixLift 4308250
  have htrace : WordTrace (prefixWord ++ tailWord_4308250) baseStart_4308250 baseEnd_4308250 := by
    simpa [prefixWord, tailWord_4308250, baseEnd_4308250] using wordTrace_append hprefix tailTrace_4308250
  have hstable : (prefixWord ++ tailWord_4308250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308250).length < 2 ^ (prefixWord ++ tailWord_4308250).sum := by decide
  have hdescent : baseEnd_4308250 < baseStart_4308250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308254 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_4308254 : Nat := 118140960795 + 4308254 * 2 ^ 59
def prefixEnd_4308254 : Nat := 4983230072969 + 3 ^ 40 * 4308254 * 2
def baseEnd_4308254 : Nat := 245800564850610241123523

theorem tailTrace_4308254 : CollatzResearch.WordTrace tailWord_4308254 prefixEnd_4308254 245800564850610241123523 := by
  unfold tailWord_4308254
  simp only [CollatzResearch.WordTrace]
  refine ⟨19641866566742378006122477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104756621689292682699319877 19641866566742378006122477)
  ·
    refine ⟨7365699962528391752295929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19641866566742378006122477 7365699962528391752295929)
    ·
      refine ⟨5524274971896293814221947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7365699962528391752295929 5524274971896293814221947)
      ·
        refine ⟨8286412457844440721332921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524274971896293814221947 8286412457844440721332921)
        ·
          refine ⟨6214809343383330540999691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8286412457844440721332921 6214809343383330540999691)
          ·
            refine ⟨9322214015074995811499537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6214809343383330540999691 9322214015074995811499537)
            ·
              refine ⟨6991660511306246858624653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9322214015074995811499537 6991660511306246858624653)
              ·
                refine ⟨2621872691739842571984245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6991660511306246858624653 2621872691739842571984245)
                ·
                  refine ⟨245800564850610241123523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621872691739842571984245 245800564850610241123523)
                  ·
                    rfl

theorem cell23_4308254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_4308254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308254 prefixEnd_4308254 := by exact prefixLift 4308254
  have htrace : WordTrace (prefixWord ++ tailWord_4308254) baseStart_4308254 baseEnd_4308254 := by
    simpa [prefixWord, tailWord_4308254, baseEnd_4308254] using wordTrace_append hprefix tailTrace_4308254
  have hstable : (prefixWord ++ tailWord_4308254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308254).length < 2 ^ (prefixWord ++ tailWord_4308254).sum := by decide
  have hdescent : baseEnd_4308254 < baseStart_4308254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308296 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_4308296 : Nat := 118140960795 + 4308296 * 2 ^ 59
def prefixEnd_4308296 : Nat := 4983230072969 + 3 ^ 40 * 4308296 * 2
def baseEnd_4308296 : Nat := 2212226649842981005786513

theorem tailTrace_4308296 : CollatzResearch.WordTrace tailWord_4308296 prefixEnd_4308296 2212226649842981005786513 := by
  unfold tailWord_4308296
  simp only [CollatzResearch.WordTrace]
  refine ⟨78568232199893432611004371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104757642933191243481339161 78568232199893432611004371)
  ·
    refine ⟨117852348299840148916506557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78568232199893432611004371 117852348299840148916506557)
    ·
      refine ⟨44194630612440055843689959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117852348299840148916506557 44194630612440055843689959)
      ·
        refine ⟨66291945918660083765534939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44194630612440055843689959 66291945918660083765534939)
        ·
          refine ⟨99437918877990125648302409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66291945918660083765534939 99437918877990125648302409)
          ·
            refine ⟨74578439158492594236226807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99437918877990125648302409 74578439158492594236226807)
            ·
              refine ⟨111867658737738891354340211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74578439158492594236226807 111867658737738891354340211)
              ·
                refine ⟨167801488106608337031510317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111867658737738891354340211 167801488106608337031510317)
                ·
                  refine ⟨62925558039978126386816369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167801488106608337031510317 62925558039978126386816369)
                  ·
                    refine ⟨47194168529983594790112277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62925558039978126386816369 47194168529983594790112277)
                    ·
                      refine ⟨2212226649842981005786513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47194168529983594790112277 2212226649842981005786513)
                      ·
                        rfl

theorem cell23_4308296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_4308296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308296 prefixEnd_4308296 := by exact prefixLift 4308296
  have htrace : WordTrace (prefixWord ++ tailWord_4308296) baseStart_4308296 baseEnd_4308296 := by
    simpa [prefixWord, tailWord_4308296, baseEnd_4308296] using wordTrace_append hprefix tailTrace_4308296
  have hstable : (prefixWord ++ tailWord_4308296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308296).length < 2 ^ (prefixWord ++ tailWord_4308296).sum := by decide
  have hdescent : baseEnd_4308296 < baseStart_4308296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308337 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 1, 1, 3]
def baseStart_4308337 : Nat := 118140960795 + 4308337 * 2 ^ 59
def prefixEnd_4308337 : Nat := 4983230072969 + 3 ^ 40 * 4308337 * 2
def baseEnd_4308337 : Nat := 2212247702549815345373825

theorem tailTrace_4308337 : CollatzResearch.WordTrace tailWord_4308337 prefixEnd_4308337 2212247702549815345373825 := by
  unfold tailWord_4308337
  simp only [CollatzResearch.WordTrace]
  refine ⟨157137959792638329224251265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104758639861758886149500843 157137959792638329224251265)
  ·
    refine ⟨117853469844478746918188449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157137959792638329224251265 117853469844478746918188449)
    ·
      refine ⟨88390102383359060188641337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117853469844478746918188449 88390102383359060188641337)
      ·
        refine ⟨66292576787519295141481003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88390102383359060188641337 66292576787519295141481003)
        ·
          refine ⟨99438865181278942712221505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66292576787519295141481003 99438865181278942712221505)
          ·
            refine ⟨74579148885959207034166129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99438865181278942712221505 74579148885959207034166129)
            ·
              refine ⟨55934361664469405275624597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74579148885959207034166129 55934361664469405275624597)
              ·
                refine ⟨2621923203022003372294903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55934361664469405275624597 2621923203022003372294903)
                ·
                  refine ⟨3932884804533005058442355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621923203022003372294903 3932884804533005058442355)
                  ·
                    refine ⟨5899327206799507587663533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932884804533005058442355 5899327206799507587663533)
                    ·
                      refine ⟨2212247702549815345373825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899327206799507587663533 2212247702549815345373825)
                      ·
                        rfl

theorem cell23_4308337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_4308337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308337 prefixEnd_4308337 := by exact prefixLift 4308337
  have htrace : WordTrace (prefixWord ++ tailWord_4308337) baseStart_4308337 baseEnd_4308337 := by
    simpa [prefixWord, tailWord_4308337, baseEnd_4308337] using wordTrace_append hprefix tailTrace_4308337
  have hstable : (prefixWord ++ tailWord_4308337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308337).length < 2 ^ (prefixWord ++ tailWord_4308337).sum := by decide
  have hdescent : baseEnd_4308337 < baseStart_4308337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308343 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_4308343 : Nat := 118140960795 + 4308343 * 2 ^ 59
def prefixEnd_4308343 : Nat := 4983230072969 + 3 ^ 40 * 4308343 * 2
def baseEnd_4308343 : Nat := 2212250783433742321898797

theorem tailTrace_4308343 : CollatzResearch.WordTrace tailWord_4308343 prefixEnd_4308343 2212250783433742321898797 := by
  unfold tailWord_4308343
  simp only [CollatzResearch.WordTrace]
  refine ⟨157138178630616592248969683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104758785753744394832646455 157138178630616592248969683)
  ·
    refine ⟨235707267945924888373454525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157138178630616592248969683 235707267945924888373454525)
    ·
      refine ⟨88390225479721833140045447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235707267945924888373454525 88390225479721833140045447)
      ·
        refine ⟨132585338219582749710068171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88390225479721833140045447 132585338219582749710068171)
        ·
          refine ⟨198878007329374124565102257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132585338219582749710068171 198878007329374124565102257)
          ·
            refine ⟨149158505497030593423826693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198878007329374124565102257 149158505497030593423826693)
            ·
              refine ⟨27967219780693236266967505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149158505497030593423826693 27967219780693236266967505)
              ·
                refine ⟨20975414835519927200225629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27967219780693236266967505 20975414835519927200225629)
                ·
                  refine ⟨7865780563319972700084611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20975414835519927200225629 7865780563319972700084611)
                  ·
                    refine ⟨11798670844979959050126917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7865780563319972700084611 11798670844979959050126917)
                    ·
                      refine ⟨2212250783433742321898797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11798670844979959050126917 2212250783433742321898797)
                      ·
                        rfl

theorem cell23_4308343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_4308343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308343 prefixEnd_4308343 := by exact prefixLift 4308343
  have htrace : WordTrace (prefixWord ++ tailWord_4308343) baseStart_4308343 baseEnd_4308343 := by
    simpa [prefixWord, tailWord_4308343, baseEnd_4308343] using wordTrace_append hprefix tailTrace_4308343
  have hstable : (prefixWord ++ tailWord_4308343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308343).length < 2 ^ (prefixWord ++ tailWord_4308343).sum := by decide
  have hdescent : baseEnd_4308343 < baseStart_4308343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308360 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4308360 : Nat := 118140960795 + 4308360 * 2 ^ 59
def prefixEnd_4308360 : Nat := 4983230072969 + 3 ^ 40 * 4308360 * 2
def baseEnd_4308360 : Nat := 2212259512604868755386219

theorem tailTrace_4308360 : CollatzResearch.WordTrace tailWord_4308360 prefixEnd_4308360 2212259512604868755386219 := by
  unfold tailWord_4308360
  simp only [CollatzResearch.WordTrace]
  refine ⟨78569399335777502076169267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104759199114370002768225689 78569399335777502076169267)
  ·
    refine ⟨117854099003666253114253901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78569399335777502076169267 117854099003666253114253901)
    ·
      refine ⟨44195287126374844917845213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117854099003666253114253901 44195287126374844917845213)
      ·
        refine ⟨16573232672390566844191955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44195287126374844917845213 16573232672390566844191955)
        ·
          refine ⟨24859849008585850266287933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16573232672390566844191955 24859849008585850266287933)
          ·
            refine ⟨9322443378219693849857975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24859849008585850266287933 9322443378219693849857975)
            ·
              refine ⟨13983665067329540774786963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322443378219693849857975 13983665067329540774786963)
              ·
                refine ⟨20975497600994311162180445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13983665067329540774786963 20975497600994311162180445)
                ·
                  refine ⟨7865811600372866685817667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20975497600994311162180445 7865811600372866685817667)
                  ·
                    refine ⟨11798717400559300028726501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7865811600372866685817667 11798717400559300028726501)
                    ·
                      refine ⟨2212259512604868755386219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11798717400559300028726501 2212259512604868755386219)
                      ·
                        rfl

theorem cell23_4308360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4308360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308360 prefixEnd_4308360 := by exact prefixLift 4308360
  have htrace : WordTrace (prefixWord ++ tailWord_4308360) baseStart_4308360 baseEnd_4308360 := by
    simpa [prefixWord, tailWord_4308360, baseEnd_4308360] using wordTrace_append hprefix tailTrace_4308360
  have hstable : (prefixWord ++ tailWord_4308360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308360).length < 2 ^ (prefixWord ++ tailWord_4308360).sum := by decide
  have hdescent : baseEnd_4308360 < baseStart_4308360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308373 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4308373 : Nat := 118140960795 + 4308373 * 2 ^ 59
def prefixEnd_4308373 : Nat := 4983230072969 + 3 ^ 40 * 4308373 * 2
def baseEnd_4308373 : Nat := 2212266187853377204523659

theorem tailTrace_4308373 : CollatzResearch.WordTrace tailWord_4308373 prefixEnd_4308373 2212266187853377204523659 := by
  unfold tailWord_4308373
  simp only [CollatzResearch.WordTrace]
  refine ⟨157139272820507907372561773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104759515213671938248374515 157139272820507907372561773)
  ·
    refine ⟨58927227307690465264710665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157139272820507907372561773 58927227307690465264710665)
    ·
      refine ⟨44195420480767848948532999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58927227307690465264710665 44195420480767848948532999)
      ·
        refine ⟨66293130721151773422799499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44195420480767848948532999 66293130721151773422799499)
        ·
          refine ⟨99439696081727660134199249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66293130721151773422799499 99439696081727660134199249)
          ·
            refine ⟨74579772061295745100649437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99439696081727660134199249 74579772061295745100649437)
            ·
              refine ⟨27967414522985904412743539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74579772061295745100649437 27967414522985904412743539)
              ·
                refine ⟨41951121784478856619115309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27967414522985904412743539 41951121784478856619115309)
                ·
                  refine ⟨15731670669179571232168241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41951121784478856619115309 15731670669179571232168241)
                  ·
                    refine ⟨11798753001884678424126181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15731670669179571232168241 11798753001884678424126181)
                    ·
                      refine ⟨2212266187853377204523659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11798753001884678424126181 2212266187853377204523659)
                      ·
                        rfl

theorem cell23_4308373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4308373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308373 prefixEnd_4308373 := by exact prefixLift 4308373
  have htrace : WordTrace (prefixWord ++ tailWord_4308373) baseStart_4308373 baseEnd_4308373 := by
    simpa [prefixWord, tailWord_4308373, baseEnd_4308373] using wordTrace_append hprefix tailTrace_4308373
  have hstable : (prefixWord ++ tailWord_4308373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308373).length < 2 ^ (prefixWord ++ tailWord_4308373).sum := by decide
  have hdescent : baseEnd_4308373 < baseStart_4308373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308377 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 1, 1, 4]
def baseStart_4308377 : Nat := 118140960795 + 4308377 * 2 ^ 59
def prefixEnd_4308377 : Nat := 4983230072969 + 3 ^ 40 * 4308377 * 2
def baseEnd_4308377 : Nat := 2212268241775995188873641

theorem tailTrace_4308377 : CollatzResearch.WordTrace tailWord_4308377 prefixEnd_4308377 2212268241775995188873641 := by
  unfold tailWord_4308377
  simp only [CollatzResearch.WordTrace]
  refine ⟨157139418712493416055707385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104759612474995610703804923 157139418712493416055707385)
  ·
    refine ⟨117854564034370062041780539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157139418712493416055707385 117854564034370062041780539)
    ·
      refine ⟨176781846051555093062670809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117854564034370062041780539 176781846051555093062670809)
      ·
        refine ⟨132586384538666319797003107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176781846051555093062670809 132586384538666319797003107)
        ·
          refine ⟨198879576807999479695504661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132586384538666319797003107 198879576807999479695504661)
          ·
            refine ⟨9322480162874975610726781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 198879576807999479695504661 9322480162874975610726781)
            ·
              refine ⟨3495930061078115854022543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9322480162874975610726781 3495930061078115854022543)
              ·
                refine ⟨5243895091617173781033815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495930061078115854022543 5243895091617173781033815)
                ·
                  refine ⟨7865842637425760671550723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243895091617173781033815 7865842637425760671550723)
                  ·
                    refine ⟨11798763956138641007326085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7865842637425760671550723 11798763956138641007326085)
                    ·
                      refine ⟨2212268241775995188873641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11798763956138641007326085 2212268241775995188873641)
                      ·
                        rfl

theorem cell23_4308377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_4308377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308377 prefixEnd_4308377 := by exact prefixLift 4308377
  have htrace : WordTrace (prefixWord ++ tailWord_4308377) baseStart_4308377 baseEnd_4308377 := by
    simpa [prefixWord, tailWord_4308377, baseEnd_4308377] using wordTrace_append hprefix tailTrace_4308377
  have hstable : (prefixWord ++ tailWord_4308377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308377).length < 2 ^ (prefixWord ++ tailWord_4308377).sum := by decide
  have hdescent : baseEnd_4308377 < baseStart_4308377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308397 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4308397 : Nat := 118140960795 + 4308397 * 2 ^ 59
def prefixEnd_4308397 : Nat := 4983230072969 + 3 ^ 40 * 4308397 * 2
def baseEnd_4308397 : Nat := 2212278511389085110623549

theorem tailTrace_4308397 : CollatzResearch.WordTrace tailWord_4308397 prefixEnd_4308397 2212278511389085110623549 := by
  unfold tailWord_4308397
  simp only [CollatzResearch.WordTrace]
  refine ⟨157140148172420959471435445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104760098781613972980956963 157140148172420959471435445)
  ·
    refine ⟨14731888891164464950447073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157140148172420959471435445 14731888891164464950447073)
    ·
      refine ⟨11048916668373348712835305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14731888891164464950447073 11048916668373348712835305)
      ·
        refine ⟨8286687501280011534626479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11048916668373348712835305 8286687501280011534626479)
        ·
          refine ⟨12430031251920017301939719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8286687501280011534626479 12430031251920017301939719)
          ·
            refine ⟨18645046877880025952909579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12430031251920017301939719 18645046877880025952909579)
            ·
              refine ⟨27967570316820038929364369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18645046877880025952909579 27967570316820038929364369)
              ·
                refine ⟨20975677737615029197023277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27967570316820038929364369 20975677737615029197023277)
                ·
                  refine ⟨7865879151605635948883729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20975677737615029197023277 7865879151605635948883729)
                  ·
                    refine ⟨5899409363704226961662797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7865879151605635948883729 5899409363704226961662797)
                    ·
                      refine ⟨2212278511389085110623549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899409363704226961662797 2212278511389085110623549)
                      ·
                        rfl

theorem cell23_4308397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4308397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308397 prefixEnd_4308397 := by exact prefixLift 4308397
  have htrace : WordTrace (prefixWord ++ tailWord_4308397) baseStart_4308397 baseEnd_4308397 := by
    simpa [prefixWord, tailWord_4308397, baseEnd_4308397] using wordTrace_append hprefix tailTrace_4308397
  have hstable : (prefixWord ++ tailWord_4308397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308397).length < 2 ^ (prefixWord ++ tailWord_4308397).sum := by decide
  have hdescent : baseEnd_4308397 < baseStart_4308397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308410 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_4308410 : Nat := 118140960795 + 4308410 * 2 ^ 59
def prefixEnd_4308410 : Nat := 4983230072969 + 3 ^ 40 * 4308410 * 2
def baseEnd_4308410 : Nat := 2212285186637593559760989

theorem tailTrace_4308410 : CollatzResearch.WordTrace tailWord_4308410 prefixEnd_4308410 2212285186637593559760989 := by
  unfold tailWord_4308410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39285155580343465672914671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104760414880915908461105789 39285155580343465672914671)
  ·
    refine ⟨58927733370515198509372007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39285155580343465672914671 58927733370515198509372007)
    ·
      refine ⟨88391600055772797764058011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58927733370515198509372007 88391600055772797764058011)
      ·
        refine ⟨132587400083659196646087017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88391600055772797764058011 132587400083659196646087017)
        ·
          refine ⟨99440550062744397484565263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132587400083659196646087017 99440550062744397484565263)
          ·
            refine ⟨149160825094116596226847895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99440550062744397484565263 149160825094116596226847895)
            ·
              refine ⟨223741237641174894340271843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149160825094116596226847895 223741237641174894340271843)
              ·
                refine ⟨335611856461762341510407765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223741237641174894340271843 335611856461762341510407765)
                ·
                  refine ⟨3932951442911277439575091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 335611856461762341510407765 3932951442911277439575091)
                  ·
                    refine ⟨5899427164366916159362637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932951442911277439575091 5899427164366916159362637)
                    ·
                      refine ⟨2212285186637593559760989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899427164366916159362637 2212285186637593559760989)
                      ·
                        rfl

theorem cell23_4308410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_4308410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308410 prefixEnd_4308410 := by exact prefixLift 4308410
  have htrace : WordTrace (prefixWord ++ tailWord_4308410) baseStart_4308410 baseEnd_4308410 := by
    simpa [prefixWord, tailWord_4308410, baseEnd_4308410] using wordTrace_append hprefix tailTrace_4308410
  have hstable : (prefixWord ++ tailWord_4308410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308410).length < 2 ^ (prefixWord ++ tailWord_4308410).sum := by decide
  have hdescent : baseEnd_4308410 < baseStart_4308410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308413 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_4308413 : Nat := 118140960795 + 4308413 * 2 ^ 59
def prefixEnd_4308413 : Nat := 4983230072969 + 3 ^ 40 * 4308413 * 2
def baseEnd_4308413 : Nat := 737428909026519016007825

theorem tailTrace_4308413 : CollatzResearch.WordTrace tailWord_4308413 prefixEnd_4308413 737428909026519016007825 := by
  unfold tailWord_4308413
  simp only [CollatzResearch.WordTrace]
  refine ⟨157140731740362994204017893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104760487826908662802678595 157140731740362994204017893)
  ·
    refine ⟨29463887201318061413253355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157140731740362994204017893 29463887201318061413253355)
    ·
      refine ⟨44195830801977092119880033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29463887201318061413253355 44195830801977092119880033)
      ·
        refine ⟨33146873101482819089910025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44195830801977092119880033 33146873101482819089910025)
        ·
          refine ⟨24860154826112114317432519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33146873101482819089910025 24860154826112114317432519)
          ·
            refine ⟨37290232239168171476148779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24860154826112114317432519 37290232239168171476148779)
            ·
              refine ⟨55935348358752257214223169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37290232239168171476148779 55935348358752257214223169)
              ·
                refine ⟨41951511269064192910667377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55935348358752257214223169 41951511269064192910667377)
                ·
                  refine ⟨31463633451798144683000533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41951511269064192910667377 31463633451798144683000533)
                  ·
                    refine ⟨737428909026519016007825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31463633451798144683000533 737428909026519016007825)
                    ·
                      rfl

theorem cell23_4308413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_4308413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308413 prefixEnd_4308413 := by exact prefixLift 4308413
  have htrace : WordTrace (prefixWord ++ tailWord_4308413) baseStart_4308413 baseEnd_4308413 := by
    simpa [prefixWord, tailWord_4308413, baseEnd_4308413] using wordTrace_append hprefix tailTrace_4308413
  have hstable : (prefixWord ++ tailWord_4308413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308413).length < 2 ^ (prefixWord ++ tailWord_4308413).sum := by decide
  have hdescent : baseEnd_4308413 < baseStart_4308413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308423 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_4308423 : Nat := 118140960795 + 4308423 * 2 ^ 59
def prefixEnd_4308423 : Nat := 4983230072969 + 3 ^ 40 * 4308423 * 2
def baseEnd_4308423 : Nat := 2212291861886102008898429

theorem tailTrace_4308423 : CollatzResearch.WordTrace tailWord_4308423 prefixEnd_4308423 2212291861886102008898429 := by
  unfold tailWord_4308423
  simp only [CollatzResearch.WordTrace]
  refine ⟨157141096470326765911881923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104760730980217843941254615 157141096470326765911881923)
  ·
    refine ⟨235711644705490148867822885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157141096470326765911881923 235711644705490148867822885)
    ·
      refine ⟨44195933382279402912716791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235711644705490148867822885 44195933382279402912716791)
      ·
        refine ⟨66293900073419104369075187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44195933382279402912716791 66293900073419104369075187)
        ·
          refine ⟨99440850110128656553612781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66293900073419104369075187 99440850110128656553612781)
          ·
            refine ⟨37290318791298246207604793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99440850110128656553612781 37290318791298246207604793)
            ·
              refine ⟨27967739093473684655703595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37290318791298246207604793 27967739093473684655703595)
              ·
                refine ⟨41951608640210526983555393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27967739093473684655703595 41951608640210526983555393)
                ·
                  refine ⟨31463706480157895237666545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41951608640210526983555393 31463706480157895237666545)
                  ·
                    refine ⟨23597779860118421428249909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31463706480157895237666545 23597779860118421428249909)
                    ·
                      refine ⟨2212291861886102008898429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23597779860118421428249909 2212291861886102008898429)
                      ·
                        rfl

theorem cell23_4308423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_4308423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308423 prefixEnd_4308423 := by exact prefixLift 4308423
  have htrace : WordTrace (prefixWord ++ tailWord_4308423) baseStart_4308423 baseEnd_4308423 := by
    simpa [prefixWord, tailWord_4308423, baseEnd_4308423] using wordTrace_append hprefix tailTrace_4308423
  have hstable : (prefixWord ++ tailWord_4308423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308423).length < 2 ^ (prefixWord ++ tailWord_4308423).sum := by decide
  have hdescent : baseEnd_4308423 < baseStart_4308423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308461 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4308461 : Nat := 118140960795 + 4308461 * 2 ^ 59
def prefixEnd_4308461 : Nat := 4983230072969 + 3 ^ 40 * 4308461 * 2
def baseEnd_4308461 : Nat := 2212311374150972860223255

theorem tailTrace_4308461 : CollatzResearch.WordTrace tailWord_4308461 prefixEnd_4308461 2212311374150972860223255 := by
  unfold tailWord_4308461
  simp only [CollatzResearch.WordTrace]
  refine ⟨157142482444189098401765237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104761654962792732267843491 157142482444189098401765237)
  ·
    refine ⟨14732107729142727975165491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157142482444189098401765237 14732107729142727975165491)
    ·
      refine ⟨22098161593714091962748237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14732107729142727975165491 22098161593714091962748237)
      ·
        refine ⟨8286810597642784486030589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22098161593714091962748237 8286810597642784486030589)
        ·
          refine ⟨3107553974116044182261471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8286810597642784486030589 3107553974116044182261471)
          ·
            refine ⟨4661330961174066273392207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107553974116044182261471 4661330961174066273392207)
            ·
              refine ⟨6991996441761099410088311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661330961174066273392207 6991996441761099410088311)
              ·
                refine ⟨10487994662641649115132467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6991996441761099410088311 10487994662641649115132467)
                ·
                  refine ⟨15731991993962473672698701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10487994662641649115132467 15731991993962473672698701)
                  ·
                    refine ⟨5899496997735927627262013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15731991993962473672698701 5899496997735927627262013)
                    ·
                      refine ⟨2212311374150972860223255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899496997735927627262013 2212311374150972860223255)
                      ·
                        rfl

theorem cell23_4308461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4308461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308461 prefixEnd_4308461 := by exact prefixLift 4308461
  have htrace : WordTrace (prefixWord ++ tailWord_4308461) baseStart_4308461 baseEnd_4308461 := by
    simpa [prefixWord, tailWord_4308461, baseEnd_4308461] using wordTrace_append hprefix tailTrace_4308461
  have hstable : (prefixWord ++ tailWord_4308461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308461).length < 2 ^ (prefixWord ++ tailWord_4308461).sum := by decide
  have hdescent : baseEnd_4308461 < baseStart_4308461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308537 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_4308537 : Nat := 118140960795 + 4308537 * 2 ^ 59
def prefixEnd_4308537 : Nat := 4983230072969 + 3 ^ 40 * 4308537 * 2
def baseEnd_4308537 : Nat := 737450132893571520957635

theorem tailTrace_4308537 : CollatzResearch.WordTrace tailWord_4308537 prefixEnd_4308537 737450132893571520957635 := by
  unfold tailWord_4308537
  simp only [CollatzResearch.WordTrace]
  refine ⟨157145254391913763381531865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104763502927942508921021243 157145254391913763381531865)
  ·
    refine ⟨117858940793935322536148899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157145254391913763381531865 117858940793935322536148899)
    ·
      refine ⟨176788411190902983804223349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117858940793935322536148899 176788411190902983804223349)
      ·
        refine ⟨16573913549147154731645939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176788411190902983804223349 16573913549147154731645939)
        ·
          refine ⟨24860870323720732097468909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16573913549147154731645939 24860870323720732097468909)
          ·
            refine ⟨9322826371395274536550841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24860870323720732097468909 9322826371395274536550841)
            ·
              refine ⟨6992119778546455902413131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9322826371395274536550841 6992119778546455902413131)
              ·
                refine ⟨10488179667819683853619697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992119778546455902413131 10488179667819683853619697)
                ·
                  refine ⟨7866134750864762890214773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10488179667819683853619697 7866134750864762890214773)
                  ·
                    refine ⟨737450132893571520957635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7866134750864762890214773 737450132893571520957635)
                    ·
                      rfl

theorem cell23_4308537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_4308537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308537 prefixEnd_4308537 := by exact prefixLift 4308537
  have htrace : WordTrace (prefixWord ++ tailWord_4308537) baseStart_4308537 baseEnd_4308537 := by
    simpa [prefixWord, tailWord_4308537, baseEnd_4308537] using wordTrace_append hprefix tailTrace_4308537
  have hstable : (prefixWord ++ tailWord_4308537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308537).length < 2 ^ (prefixWord ++ tailWord_4308537).sum := by decide
  have hdescent : baseEnd_4308537 < baseStart_4308537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308584 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_4308584 : Nat := 118140960795 + 4308584 * 2 ^ 59
def prefixEnd_4308584 : Nat := 4983230072969 + 3 ^ 40 * 4308584 * 2
def baseEnd_4308584 : Nat := 737458177423825292995063

theorem tailTrace_4308584 : CollatzResearch.WordTrace tailWord_4308584 prefixEnd_4308584 737458177423825292995063 := by
  unfold tailWord_4308584
  simp only [CollatzResearch.WordTrace]
  refine ⟨78573484311371745204246403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104764645748495660272328537 78573484311371745204246403)
  ·
    refine ⟨117860226467057617806369605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78573484311371745204246403 117860226467057617806369605)
    ·
      refine ⟨22098792462573303338694301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117860226467057617806369605 22098792462573303338694301)
      ·
        refine ⟨8287047173464988752010363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22098792462573303338694301 8287047173464988752010363)
        ·
          refine ⟨12430570760197483128015545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8287047173464988752010363 12430570760197483128015545)
          ·
            refine ⟨9322928070148112346011659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12430570760197483128015545 9322928070148112346011659)
            ·
              refine ⟨13984392105222168519017489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322928070148112346011659 13984392105222168519017489)
              ·
                refine ⟨10488294078916626389263117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13984392105222168519017489 10488294078916626389263117)
                ·
                  refine ⟨3933110279593734895973669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10488294078916626389263117 3933110279593734895973669)
                  ·
                    refine ⟨737458177423825292995063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933110279593734895973669 737458177423825292995063)
                    ·
                      rfl

theorem cell23_4308584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_4308584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308584 prefixEnd_4308584 := by exact prefixLift 4308584
  have htrace : WordTrace (prefixWord ++ tailWord_4308584) baseStart_4308584 baseEnd_4308584 := by
    simpa [prefixWord, tailWord_4308584, baseEnd_4308584] using wordTrace_append hprefix tailTrace_4308584
  have hstable : (prefixWord ++ tailWord_4308584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308584).length < 2 ^ (prefixWord ++ tailWord_4308584).sum := by decide
  have hdescent : baseEnd_4308584 < baseStart_4308584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308594 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4308594 : Nat := 118140960795 + 4308594 * 2 ^ 59
def prefixEnd_4308594 : Nat := 4983230072969 + 3 ^ 40 * 4308594 * 2
def baseEnd_4308594 : Nat := 2212379667078020839860143

theorem tailTrace_4308594 : CollatzResearch.WordTrace tailWord_4308594 prefixEnd_4308594 2212379667078020839860143 := by
  unfold tailWord_4308594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39286833338176815529089209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104764888901804841410904557 39286833338176815529089209)
  ·
    refine ⟨29465125003632611646816907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39286833338176815529089209 29465125003632611646816907)
    ·
      refine ⟨44197687505448917470225361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29465125003632611646816907 44197687505448917470225361)
      ·
        refine ⟨33148265629086688102669021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44197687505448917470225361 33148265629086688102669021)
        ·
          refine ⟨12430599610907508038500883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33148265629086688102669021 12430599610907508038500883)
          ·
            refine ⟨18645899416361262057751325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12430599610907508038500883 18645899416361262057751325)
            ·
              refine ⟨6992212281135473271656747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18645899416361262057751325 6992212281135473271656747)
              ·
                refine ⟨10488318421703209907485121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992212281135473271656747 10488318421703209907485121)
                ·
                  refine ⟨7866238816277407430613841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10488318421703209907485121 7866238816277407430613841)
                  ·
                    refine ⟨5899679112208055572960381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7866238816277407430613841 5899679112208055572960381)
                    ·
                      refine ⟨2212379667078020839860143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899679112208055572960381 2212379667078020839860143)
                      ·
                        rfl

theorem cell23_4308594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4308594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308594 prefixEnd_4308594 := by exact prefixLift 4308594
  have htrace : WordTrace (prefixWord ++ tailWord_4308594) baseStart_4308594 baseEnd_4308594 := by
    simpa [prefixWord, tailWord_4308594, baseEnd_4308594] using wordTrace_append hprefix tailTrace_4308594
  have hstable : (prefixWord ++ tailWord_4308594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308594).length < 2 ^ (prefixWord ++ tailWord_4308594).sum := by decide
  have hdescent : baseEnd_4308594 < baseStart_4308594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308644 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_4308644 : Nat := 118140960795 + 4308644 * 2 ^ 59
def prefixEnd_4308644 : Nat := 4983230072969 + 3 ^ 40 * 4308644 * 2
def baseEnd_4308644 : Nat := 737468447036915214744971

theorem tailTrace_4308644 : CollatzResearch.WordTrace tailWord_4308644 prefixEnd_4308644 737468447036915214744971 := by
  unfold tailWord_4308644
  simp only [CollatzResearch.WordTrace]
  refine ⟨78574578501263060327838493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104766104668350747103784657 78574578501263060327838493)
  ·
    refine ⟨29465466937973647622939435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78574578501263060327838493 29465466937973647622939435)
    ·
      refine ⟨44198200406960471434409153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29465466937973647622939435 44198200406960471434409153)
      ·
        refine ⟨33148650305220353575806865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44198200406960471434409153 33148650305220353575806865)
        ·
          refine ⟨24861487728915265181855149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33148650305220353575806865 24861487728915265181855149)
          ·
            refine ⟨9323057898343224443195681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24861487728915265181855149 9323057898343224443195681)
            ·
              refine ⟨6992293423757418332396761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9323057898343224443195681 6992293423757418332396761)
              ·
                refine ⟨5244220067818063749297571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6992293423757418332396761 5244220067818063749297571)
                ·
                  refine ⟨7866330101727095623946357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244220067818063749297571 7866330101727095623946357)
                  ·
                    refine ⟨737468447036915214744971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7866330101727095623946357 737468447036915214744971)
                    ·
                      rfl

theorem cell23_4308644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_4308644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308644 prefixEnd_4308644 := by exact prefixLift 4308644
  have htrace : WordTrace (prefixWord ++ tailWord_4308644) baseStart_4308644 baseEnd_4308644 := by
    simpa [prefixWord, tailWord_4308644, baseEnd_4308644] using wordTrace_append hprefix tailTrace_4308644
  have hstable : (prefixWord ++ tailWord_4308644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308644).length < 2 ^ (prefixWord ++ tailWord_4308644).sum := by decide
  have hdescent : baseEnd_4308644 < baseStart_4308644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308664 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_4308664 : Nat := 118140960795 + 4308664 * 2 ^ 59
def prefixEnd_4308664 : Nat := 4983230072969 + 3 ^ 40 * 4308664 * 2
def baseEnd_4308664 : Nat := 2212415610723835565984821

theorem tailTrace_4308664 : CollatzResearch.WordTrace tailWord_4308664 prefixEnd_4308664 2212415610723835565984821 := by
  unfold tailWord_4308664
  simp only [CollatzResearch.WordTrace]
  refine ⟨78574943231226832035702523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104766590974969109380936697 78574943231226832035702523)
  ·
    refine ⟨117862414846840248053553785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78574943231226832035702523 117862414846840248053553785)
    ·
      refine ⟨88396811135130186040165339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117862414846840248053553785 88396811135130186040165339)
      ·
        refine ⟨132595216702695279060248009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88396811135130186040165339 132595216702695279060248009)
        ·
          refine ⟨99446412527021459295186007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132595216702695279060248009 99446412527021459295186007)
          ·
            refine ⟨149169618790532188942779011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99446412527021459295186007 149169618790532188942779011)
            ·
              refine ⟨223754428185798283414168517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149169618790532188942779011 223754428185798283414168517)
              ·
                refine ⟨41953955284837178140156597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223754428185798283414168517 41953955284837178140156597)
                ·
                  refine ⟨3933183307953485450639681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41953955284837178140156597 3933183307953485450639681)
                  ·
                    refine ⟨2949887480965114087979761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3933183307953485450639681 2949887480965114087979761)
                    ·
                      refine ⟨2212415610723835565984821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949887480965114087979761 2212415610723835565984821)
                      ·
                        rfl

theorem cell23_4308664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_4308664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308664 prefixEnd_4308664 := by exact prefixLift 4308664
  have htrace : WordTrace (prefixWord ++ tailWord_4308664) baseStart_4308664 baseEnd_4308664 := by
    simpa [prefixWord, tailWord_4308664, baseEnd_4308664] using wordTrace_append hprefix tailTrace_4308664
  have hstable : (prefixWord ++ tailWord_4308664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308664).length < 2 ^ (prefixWord ++ tailWord_4308664).sum := by decide
  have hdescent : baseEnd_4308664 < baseStart_4308664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308711 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4308711 : Nat := 118140960795 + 4308711 * 2 ^ 59
def prefixEnd_4308711 : Nat := 4983230072969 + 3 ^ 40 * 4308711 * 2
def baseEnd_4308711 : Nat := 2212439744314596882097105

theorem tailTrace_4308711 : CollatzResearch.WordTrace tailWord_4308711 prefixEnd_4308711 2212439744314596882097105 := by
  unfold tailWord_4308711
  simp only [CollatzResearch.WordTrace]
  refine ⟨157151600693283391098365987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104767733795522260732243991 157151600693283391098365987)
  ·
    refine ⟨235727401039925086647548981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157151600693283391098365987 235727401039925086647548981)
    ·
      refine ⟨22099443847492976873207717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235727401039925086647548981 22099443847492976873207717)
      ·
        refine ⟨4143645721404933163726447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22099443847492976873207717 4143645721404933163726447)
        ·
          refine ⟨6215468582107399745589671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143645721404933163726447 6215468582107399745589671)
          ·
            refine ⟨9323202873161099618384507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215468582107399745589671 9323202873161099618384507)
            ·
              refine ⟨13984804309741649427576761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9323202873161099618384507 13984804309741649427576761)
              ·
                refine ⟨10488603232306237070682571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13984804309741649427576761 10488603232306237070682571)
                ·
                  refine ⟨15732904848459355606023857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10488603232306237070682571 15732904848459355606023857)
                  ·
                    refine ⟨11799678636344516704517893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15732904848459355606023857 11799678636344516704517893)
                    ·
                      refine ⟨2212439744314596882097105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11799678636344516704517893 2212439744314596882097105)
                      ·
                        rfl

theorem cell23_4308711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4308711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308711 prefixEnd_4308711 := by exact prefixLift 4308711
  have htrace : WordTrace (prefixWord ++ tailWord_4308711) baseStart_4308711 baseEnd_4308711 := by
    simpa [prefixWord, tailWord_4308711, baseEnd_4308711] using wordTrace_append hprefix tailTrace_4308711
  have hstable : (prefixWord ++ tailWord_4308711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308711).length < 2 ^ (prefixWord ++ tailWord_4308711).sum := by decide
  have hdescent : baseEnd_4308711 < baseStart_4308711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308714 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_4308714 : Nat := 118140960795 + 4308714 * 2 ^ 59
def prefixEnd_4308714 : Nat := 4983230072969 + 3 ^ 40 * 4308714 * 2
def baseEnd_4308714 : Nat := 2212441284756560370359591

theorem tailTrace_4308714 : CollatzResearch.WordTrace tailWord_4308714 prefixEnd_4308714 2212441284756560370359591 := by
  unfold tailWord_4308714
  simp only [CollatzResearch.WordTrace]
  refine ⟨39287927528068130652681299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104767806741515015073816797 39287927528068130652681299)
  ·
    refine ⟨58931891292102195979021949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39287927528068130652681299 58931891292102195979021949)
    ·
      refine ⟨22099459234538323492133231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58931891292102195979021949 22099459234538323492133231)
      ·
        refine ⟨33149188851807485238199847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22099459234538323492133231 33149188851807485238199847)
        ·
          refine ⟨49723783277711227857299771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33149188851807485238199847 49723783277711227857299771)
          ·
            refine ⟨74585674916566841785949657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49723783277711227857299771 74585674916566841785949657)
            ·
              refine ⟨55939256187425131339462243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74585674916566841785949657 55939256187425131339462243)
              ·
                refine ⟨83908884281137697009193365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55939256187425131339462243 83908884281137697009193365)
                ·
                  refine ⟨3933228950678329547305939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83908884281137697009193365 3933228950678329547305939)
                  ·
                    refine ⟨5899843426017494320958909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933228950678329547305939 5899843426017494320958909)
                    ·
                      refine ⟨2212441284756560370359591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899843426017494320958909 2212441284756560370359591)
                      ·
                        rfl

theorem cell23_4308714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_4308714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308714 prefixEnd_4308714 := by exact prefixLift 4308714
  have htrace : WordTrace (prefixWord ++ tailWord_4308714) baseStart_4308714 baseEnd_4308714 := by
    simpa [prefixWord, tailWord_4308714, baseEnd_4308714] using wordTrace_append hprefix tailTrace_4308714
  have hstable : (prefixWord ++ tailWord_4308714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308714).length < 2 ^ (prefixWord ++ tailWord_4308714).sum := by decide
  have hdescent : baseEnd_4308714 < baseStart_4308714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308737 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4308737 : Nat := 118140960795 + 4308737 * 2 ^ 59
def prefixEnd_4308737 : Nat := 4983230072969 + 3 ^ 40 * 4308737 * 2
def baseEnd_4308737 : Nat := 2212453094811613780371985

theorem tailTrace_4308737 : CollatzResearch.WordTrace tailWord_4308737 prefixEnd_4308737 2212453094811613780371985 := by
  unfold tailWord_4308737
  simp only [CollatzResearch.WordTrace]
  refine ⟨157152548991189197538812465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104768365994126131692541643 157152548991189197538812465)
  ·
    refine ⟨117864411743391898154109349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157152548991189197538812465 117864411743391898154109349)
    ·
      refine ⟨22099577201885980903895503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117864411743391898154109349 22099577201885980903895503)
      ·
        refine ⟨33149365802828971355843255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22099577201885980903895503 33149365802828971355843255)
        ·
          refine ⟨49724048704243457033764883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33149365802828971355843255 49724048704243457033764883)
          ·
            refine ⟨74586073056365185550647325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49724048704243457033764883 74586073056365185550647325)
            ·
              refine ⟨27969777396136944581492747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74586073056365185550647325 27969777396136944581492747)
              ·
                refine ⟨41954666094205416872239121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27969777396136944581492747 41954666094205416872239121)
                ·
                  refine ⟨31465999570654062654179341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41954666094205416872239121 31465999570654062654179341)
                  ·
                    refine ⟨11799749838995273495317253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31465999570654062654179341 11799749838995273495317253)
                    ·
                      refine ⟨2212453094811613780371985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11799749838995273495317253 2212453094811613780371985)
                      ·
                        rfl

theorem cell23_4308737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4308737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308737 prefixEnd_4308737 := by exact prefixLift 4308737
  have htrace : WordTrace (prefixWord ++ tailWord_4308737) baseStart_4308737 baseEnd_4308737 := by
    simpa [prefixWord, tailWord_4308737, baseEnd_4308737] using wordTrace_append hprefix tailTrace_4308737
  have hstable : (prefixWord ++ tailWord_4308737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308737).length < 2 ^ (prefixWord ++ tailWord_4308737).sum := by decide
  have hdescent : baseEnd_4308737 < baseStart_4308737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308742 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4308742 : Nat := 118140960795 + 4308742 * 2 ^ 59
def prefixEnd_4308742 : Nat := 4983230072969 + 3 ^ 40 * 4308742 * 2
def baseEnd_4308742 : Nat := 737485220738295420269821

theorem tailTrace_4308742 : CollatzResearch.WordTrace tailWord_4308742 prefixEnd_4308742 737485220738295420269821 := by
  unfold tailWord_4308742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4911022854880346356023265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104768487570780722261829653 4911022854880346356023265)
  ·
    refine ⟨3683267141160259767017449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4911022854880346356023265 3683267141160259767017449)
    ·
      refine ⟨2762450355870194825263087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3683267141160259767017449 2762450355870194825263087)
      ·
        refine ⟨4143675533805292237894631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762450355870194825263087 4143675533805292237894631)
        ·
          refine ⟨6215513300707938356841947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143675533805292237894631 6215513300707938356841947)
          ·
            refine ⟨9323269951061907535262921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215513300707938356841947 9323269951061907535262921)
            ·
              refine ⟨6992452463296430651447191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9323269951061907535262921 6992452463296430651447191)
              ·
                refine ⟨10488678694944645977170787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992452463296430651447191 10488678694944645977170787)
                ·
                  refine ⟨15733018042416968965756181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10488678694944645977170787 15733018042416968965756181)
                  ·
                    refine ⟨737485220738295420269821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15733018042416968965756181 737485220738295420269821)
                    ·
                      rfl

theorem cell23_4308742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4308742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308742 prefixEnd_4308742 := by exact prefixLift 4308742
  have htrace : WordTrace (prefixWord ++ tailWord_4308742) baseStart_4308742 baseEnd_4308742 := by
    simpa [prefixWord, tailWord_4308742, baseEnd_4308742] using wordTrace_append hprefix tailTrace_4308742
  have hstable : (prefixWord ++ tailWord_4308742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308742).length < 2 ^ (prefixWord ++ tailWord_4308742).sum := by decide
  have hdescent : baseEnd_4308742 < baseStart_4308742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308749 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4308749 : Nat := 118140960795 + 4308749 * 2 ^ 59
def prefixEnd_4308749 : Nat := 4983230072969 + 3 ^ 40 * 4308749 * 2
def baseEnd_4308749 : Nat := 2212459256579467733421931

theorem tailTrace_4308749 : CollatzResearch.WordTrace tailWord_4308749 prefixEnd_4308749 2212459256579467733421931 := by
  unfold tailWord_4308749
  simp only [CollatzResearch.WordTrace]
  refine ⟨157152986667145723588249301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104768657778097149058832867 157152986667145723588249301)
  ·
    refine ⟨3683273125011227896599593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 157152986667145723588249301 3683273125011227896599593)
    ·
      refine ⟨2762454843758420922449695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3683273125011227896599593 2762454843758420922449695)
      ·
        refine ⟨4143682265637631383674543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762454843758420922449695 4143682265637631383674543)
        ·
          refine ⟨6215523398456447075511815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143682265637631383674543 6215523398456447075511815)
          ·
            refine ⟨9323285097684670613267723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215523398456447075511815 9323285097684670613267723)
            ·
              refine ⟨13984927646527005919901585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9323285097684670613267723 13984927646527005919901585)
              ·
                refine ⟨10488695734895254439926189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13984927646527005919901585 10488695734895254439926189)
                ·
                  refine ⟨3933260900585720414972321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10488695734895254439926189 3933260900585720414972321)
                  ·
                    refine ⟨2949945675439290311229241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3933260900585720414972321 2949945675439290311229241)
                    ·
                      refine ⟨2212459256579467733421931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2949945675439290311229241 2212459256579467733421931)
                      ·
                        rfl

theorem cell23_4308749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4308749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308749 prefixEnd_4308749 := by exact prefixLift 4308749
  have htrace : WordTrace (prefixWord ++ tailWord_4308749) baseStart_4308749 baseEnd_4308749 := by
    simpa [prefixWord, tailWord_4308749, baseEnd_4308749] using wordTrace_append hprefix tailTrace_4308749
  have hstable : (prefixWord ++ tailWord_4308749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308749).length < 2 ^ (prefixWord ++ tailWord_4308749).sum := by decide
  have hdescent : baseEnd_4308749 < baseStart_4308749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308767 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_4308767 : Nat := 118140960795 + 4308767 * 2 ^ 59
def prefixEnd_4308767 : Nat := 4983230072969 + 3 ^ 40 * 4308767 * 2
def baseEnd_4308767 : Nat := 2212468499231248662996847

theorem tailTrace_4308767 : CollatzResearch.WordTrace tailWord_4308767 prefixEnd_4308767 2212468499231248662996847 := by
  unfold tailWord_4308767
  simp only [CollatzResearch.WordTrace]
  refine ⟨157153643181080512662404555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104769095454053675108269703 157153643181080512662404555)
  ·
    refine ⟨235730464771620768993606833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157153643181080512662404555 235730464771620768993606833)
    ·
      refine ⟨176797848578715576745205125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235730464771620768993606833 176797848578715576745205125)
      ·
        refine ⟨33149596608509170639725961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176797848578715576745205125 33149596608509170639725961)
        ·
          refine ⟨24862197456381877979794471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33149596608509170639725961 24862197456381877979794471)
          ·
            refine ⟨37293296184572816969691707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24862197456381877979794471 37293296184572816969691707)
            ·
              refine ⟨55939944276859225454537561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37293296184572816969691707 55939944276859225454537561)
              ·
                refine ⟨41954958207644419090903171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55939944276859225454537561 41954958207644419090903171)
                ·
                  refine ⟨62932437311466628636354757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41954958207644419090903171 62932437311466628636354757)
                  ·
                    refine ⟨11799831995899992869316517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62932437311466628636354757 11799831995899992869316517)
                    ·
                      refine ⟨2212468499231248662996847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11799831995899992869316517 2212468499231248662996847)
                      ·
                        rfl

theorem cell23_4308767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_4308767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308767 prefixEnd_4308767 := by exact prefixLift 4308767
  have htrace : WordTrace (prefixWord ++ tailWord_4308767) baseStart_4308767 baseEnd_4308767 := by
    simpa [prefixWord, tailWord_4308767, baseEnd_4308767] using wordTrace_append hprefix tailTrace_4308767
  have hstable : (prefixWord ++ tailWord_4308767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308767).length < 2 ^ (prefixWord ++ tailWord_4308767).sum := by decide
  have hdescent : baseEnd_4308767 < baseStart_4308767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308782 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4308782 : Nat := 118140960795 + 4308782 * 2 ^ 59
def prefixEnd_4308782 : Nat := 4983230072969 + 3 ^ 40 * 4308782 * 2
def baseEnd_4308782 : Nat := 2212476201441066104309279

theorem tailTrace_4308782 : CollatzResearch.WordTrace tailWord_4308782 prefixEnd_4308782 2212476201441066104309279 := by
  unfold tailWord_4308782
  simp only [CollatzResearch.WordTrace]
  refine ⟨19644273784503271278025075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104769460184017446816133733 19644273784503271278025075)
  ·
    refine ⟨29466410676754906917037613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19644273784503271278025075 29466410676754906917037613)
    ·
      refine ⟨11049904003783090093889105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29466410676754906917037613 11049904003783090093889105)
      ·
        refine ⟨8287428002837317570416829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11049904003783090093889105 8287428002837317570416829)
        ·
          refine ⟨3107785501063994088906311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8287428002837317570416829 3107785501063994088906311)
          ·
            refine ⟨4661678251595991133359467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107785501063994088906311 4661678251595991133359467)
            ·
              refine ⟨6992517377393986700039201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661678251595991133359467 6992517377393986700039201)
              ·
                refine ⟨5244388033045490025029401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6992517377393986700039201 5244388033045490025029401)
                ·
                  refine ⟨3933291024784117518772051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5244388033045490025029401 3933291024784117518772051)
                  ·
                    refine ⟨5899936537176176278158077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933291024784117518772051 5899936537176176278158077)
                    ·
                      refine ⟨2212476201441066104309279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5899936537176176278158077 2212476201441066104309279)
                      ·
                        rfl

theorem cell23_4308782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4308782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308782 prefixEnd_4308782 := by exact prefixLift 4308782
  have htrace : WordTrace (prefixWord ++ tailWord_4308782) baseStart_4308782 baseEnd_4308782 := by
    simpa [prefixWord, tailWord_4308782, baseEnd_4308782] using wordTrace_append hprefix tailTrace_4308782
  have hstable : (prefixWord ++ tailWord_4308782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308782).length < 2 ^ (prefixWord ++ tailWord_4308782).sum := by decide
  have hdescent : baseEnd_4308782 < baseStart_4308782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308794 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_4308794 : Nat := 118140960795 + 4308794 * 2 ^ 59
def prefixEnd_4308794 : Nat := 4983230072969 + 3 ^ 40 * 4308794 * 2
def baseEnd_4308794 : Nat := 245831373689880006373247

theorem tailTrace_4308794 : CollatzResearch.WordTrace tailWord_4308794 prefixEnd_4308794 245831373689880006373247 := by
  unfold tailWord_4308794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39288656987995674068409359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104769751967988464182424957 39288656987995674068409359)
  ·
    refine ⟨58932985481993511102614039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39288656987995674068409359 58932985481993511102614039)
    ·
      refine ⟨88399478222990266653921059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58932985481993511102614039 88399478222990266653921059)
      ·
        refine ⟨132599217334485399980881589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88399478222990266653921059 132599217334485399980881589)
        ·
          refine ⟨12431176625108006248207649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132599217334485399980881589 12431176625108006248207649)
          ·
            refine ⟨9323382468831004686155737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12431176625108006248207649 9323382468831004686155737)
            ·
              refine ⟨6992536851623253514616803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9323382468831004686155737 6992536851623253514616803)
              ·
                refine ⟨10488805277434880271925205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992536851623253514616803 10488805277434880271925205)
                ·
                  refine ⟨245831373689880006373247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10488805277434880271925205 245831373689880006373247)
                  ·
                    rfl

theorem cell23_4308794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_4308794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308794 prefixEnd_4308794 := by exact prefixLift 4308794
  have htrace : WordTrace (prefixWord ++ tailWord_4308794) baseStart_4308794 baseEnd_4308794 := by
    simpa [prefixWord, tailWord_4308794, baseEnd_4308794] using wordTrace_append hprefix tailTrace_4308794
  have hstable : (prefixWord ++ tailWord_4308794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308794).length < 2 ^ (prefixWord ++ tailWord_4308794).sum := by decide
  have hdescent : baseEnd_4308794 < baseStart_4308794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308807 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 7]
def baseStart_4308807 : Nat := 118140960795 + 4308807 * 2 ^ 59
def prefixEnd_4308807 : Nat := 4983230072969 + 3 ^ 40 * 4308807 * 2
def baseEnd_4308807 : Nat := 737496346152476168832221

theorem tailTrace_4308807 : CollatzResearch.WordTrace tailWord_4308807 prefixEnd_4308807 737496346152476168832221 := by
  unfold tailWord_4308807
  simp only [CollatzResearch.WordTrace]
  refine ⟨157155102100935599493860675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104770068067290399662573783 157155102100935599493860675)
  ·
    refine ⟨235732653151403399240791013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157155102100935599493860675 235732653151403399240791013)
    ·
      refine ⟨44199872465888137357648315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235732653151403399240791013 44199872465888137357648315)
      ·
        refine ⟨66299808698832206036472473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44199872465888137357648315 66299808698832206036472473)
        ·
          refine ⟨49724856524124154527354355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66299808698832206036472473 49724856524124154527354355)
          ·
            refine ⟨74587284786186231791031533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49724856524124154527354355 74587284786186231791031533)
            ·
              refine ⟨27970231794819836921636825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74587284786186231791031533 27970231794819836921636825)
              ·
                refine ⟨20977673846114877691227619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27970231794819836921636825 20977673846114877691227619)
                ·
                  refine ⟨31466510769172316536841429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20977673846114877691227619 31466510769172316536841429)
                  ·
                    refine ⟨737496346152476168832221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31466510769172316536841429 737496346152476168832221)
                    ·
                      rfl

theorem cell23_4308807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_4308807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308807 prefixEnd_4308807 := by exact prefixLift 4308807
  have htrace : WordTrace (prefixWord ++ tailWord_4308807) baseStart_4308807 baseEnd_4308807 := by
    simpa [prefixWord, tailWord_4308807, baseEnd_4308807] using wordTrace_append hprefix tailTrace_4308807
  have hstable : (prefixWord ++ tailWord_4308807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308807).length < 2 ^ (prefixWord ++ tailWord_4308807).sum := by decide
  have hdescent : baseEnd_4308807 < baseStart_4308807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308844 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_4308844 : Nat := 118140960795 + 4308844 * 2 ^ 59
def prefixEnd_4308844 : Nat := 4983230072969 + 3 ^ 40 * 4308844 * 2
def baseEnd_4308844 : Nat := 2212508037241644861733993

theorem tailTrace_4308844 : CollatzResearch.WordTrace tailWord_4308844 prefixEnd_4308844 2212508037241644861733993 := by
  unfold tailWord_4308844
  simp only [CollatzResearch.WordTrace]
  refine ⟨78578225800900777406478793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104770967734534369875305057 78578225800900777406478793)
  ·
    refine ⟨58933669350675583054859095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78578225800900777406478793 58933669350675583054859095)
    ·
      refine ⟨88400504026013374582288643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58933669350675583054859095 88400504026013374582288643)
      ·
        refine ⟨132600756039020061873432965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88400504026013374582288643 132600756039020061873432965)
        ·
          refine ⟨24862641757316261601268681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132600756039020061873432965 24862641757316261601268681)
          ·
            refine ⟨18646981317987196200951511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24862641757316261601268681 18646981317987196200951511)
            ·
              refine ⟨27970471976980794301427267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18646981317987196200951511 27970471976980794301427267)
              ·
                refine ⟨41955707965471191452140901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27970471976980794301427267 41955707965471191452140901)
                ·
                  refine ⟨7866695243525848397276419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41955707965471191452140901 7866695243525848397276419)
                  ·
                    refine ⟨11800042865288772595914629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7866695243525848397276419 11800042865288772595914629)
                    ·
                      refine ⟨2212508037241644861733993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11800042865288772595914629 2212508037241644861733993)
                      ·
                        rfl

theorem cell23_4308844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_4308844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308844 prefixEnd_4308844 := by exact prefixLift 4308844
  have htrace : WordTrace (prefixWord ++ tailWord_4308844) baseStart_4308844 baseEnd_4308844 := by
    simpa [prefixWord, tailWord_4308844, baseEnd_4308844] using wordTrace_append hprefix tailTrace_4308844
  have hstable : (prefixWord ++ tailWord_4308844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308844).length < 2 ^ (prefixWord ++ tailWord_4308844).sum := by decide
  have hdescent : baseEnd_4308844 < baseStart_4308844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308864 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_4308864 : Nat := 118140960795 + 4308864 * 2 ^ 59
def prefixEnd_4308864 : Nat := 4983230072969 + 3 ^ 40 * 4308864 * 2
def baseEnd_4308864 : Nat := 2212518306854734783483901

theorem tailTrace_4308864 : CollatzResearch.WordTrace tailWord_4308864 prefixEnd_4308864 2212518306854734783483901 := by
  unfold tailWord_4308864
  simp only [CollatzResearch.WordTrace]
  refine ⟨78578590530864549114342823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104771454041152732152457097 78578590530864549114342823)
  ·
    refine ⟨117867885796296823671514235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78578590530864549114342823 117867885796296823671514235)
    ·
      refine ⟨176801828694445235507271353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117867885796296823671514235 176801828694445235507271353)
      ·
        refine ⟨132601371520833926630453515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176801828694445235507271353 132601371520833926630453515)
        ·
          refine ⟨198902057281250889945680273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132601371520833926630453515 198902057281250889945680273)
          ·
            refine ⟨149176542960938167459260205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198902057281250889945680273 149176542960938167459260205)
            ·
              refine ⟨55941203610351812797222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149176542960938167459260205 55941203610351812797222577)
              ·
                refine ⟨41955902707763859597916933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55941203610351812797222577 41955902707763859597916933)
                ·
                  refine ⟨7866731757705723674609425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41955902707763859597916933 7866731757705723674609425)
                  ·
                    refine ⟨5900048818279292755957069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7866731757705723674609425 5900048818279292755957069)
                    ·
                      refine ⟨2212518306854734783483901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900048818279292755957069 2212518306854734783483901)
                      ·
                        rfl

theorem cell23_4308864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_4308864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308864 prefixEnd_4308864 := by exact prefixLift 4308864
  have htrace : WordTrace (prefixWord ++ tailWord_4308864) baseStart_4308864 baseEnd_4308864 := by
    simpa [prefixWord, tailWord_4308864, baseEnd_4308864] using wordTrace_append hprefix tailTrace_4308864
  have hstable : (prefixWord ++ tailWord_4308864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308864).length < 2 ^ (prefixWord ++ tailWord_4308864).sum := by decide
  have hdescent : baseEnd_4308864 < baseStart_4308864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308907 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_4308907 : Nat := 118140960795 + 4308907 * 2 ^ 59
def prefixEnd_4308907 : Nat := 4983230072969 + 3 ^ 40 * 4308907 * 2
def baseEnd_4308907 : Nat := 2212540386522878115246203

theorem tailTrace_4308907 : CollatzResearch.WordTrace tailWord_4308907 prefixEnd_4308907 2212540386522878115246203 := by
  unfold tailWord_4308907
  simp only [CollatzResearch.WordTrace]
  refine ⟨157158749400573316572500975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104772499600382211048333983 157158749400573316572500975)
  ·
    refine ⟨235738124100859974858751463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157158749400573316572500975 235738124100859974858751463)
    ·
      refine ⟨353607186151289962288127195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235738124100859974858751463 353607186151289962288127195)
      ·
        refine ⟨530410779226934943432190793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353607186151289962288127195 530410779226934943432190793)
        ·
          refine ⟨397808084420201207574143095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530410779226934943432190793 397808084420201207574143095)
          ·
            refine ⟨596712126630301811361214643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397808084420201207574143095 596712126630301811361214643)
            ·
              refine ⟨895068189945452717041821965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596712126630301811361214643 895068189945452717041821965)
              ·
                refine ⟨335650571229544768890683237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 895068189945452717041821965 335650571229544768890683237)
                ·
                  refine ⟨62934482105539644167003107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335650571229544768890683237 62934482105539644167003107)
                  ·
                    refine ⟨94401723158309466250504661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62934482105539644167003107 94401723158309466250504661)
                    ·
                      refine ⟨2212540386522878115246203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94401723158309466250504661 2212540386522878115246203)
                      ·
                        rfl

theorem cell23_4308907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_4308907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308907 prefixEnd_4308907 := by exact prefixLift 4308907
  have htrace : WordTrace (prefixWord ++ tailWord_4308907) baseStart_4308907 baseEnd_4308907 := by
    simpa [prefixWord, tailWord_4308907, baseEnd_4308907] using wordTrace_append hprefix tailTrace_4308907
  have hstable : (prefixWord ++ tailWord_4308907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308907).length < 2 ^ (prefixWord ++ tailWord_4308907).sum := by decide
  have hdescent : baseEnd_4308907 < baseStart_4308907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308911 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 3]
def baseStart_4308911 : Nat := 118140960795 + 4308911 * 2 ^ 59
def prefixEnd_4308911 : Nat := 4983230072969 + 3 ^ 40 * 4308911 * 2
def baseEnd_4308911 : Nat := 2212542440445496099596185

theorem tailTrace_4308911 : CollatzResearch.WordTrace tailWord_4308911 prefixEnd_4308911 2212542440445496099596185 := by
  unfold tailWord_4308911
  simp only [CollatzResearch.WordTrace]
  refine ⟨157158895292558825255646587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104772596861705883503764391 157158895292558825255646587)
  ·
    refine ⟨235738342938838237883469881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157158895292558825255646587 235738342938838237883469881)
    ·
      refine ⟨176803757204128678412602411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235738342938838237883469881 176803757204128678412602411)
      ·
        refine ⟨265205635806193017618903617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176803757204128678412602411 265205635806193017618903617)
        ·
          refine ⟨198904226854644763214177713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265205635806193017618903617 198904226854644763214177713)
          ·
            refine ⟨149178170140983572410633285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198904226854644763214177713 149178170140983572410633285)
            ·
              refine ⟨27970906901434419826993741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149178170140983572410633285 27970906901434419826993741)
              ·
                refine ⟨10489090088037907435122653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27970906901434419826993741 10489090088037907435122653)
                ·
                  refine ⟨3933408783014215288170995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10489090088037907435122653 3933408783014215288170995)
                  ·
                    refine ⟨5900113174521322932256493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933408783014215288170995 5900113174521322932256493)
                    ·
                      refine ⟨2212542440445496099596185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900113174521322932256493 2212542440445496099596185)
                      ·
                        rfl

theorem cell23_4308911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_4308911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308911 prefixEnd_4308911 := by exact prefixLift 4308911
  have htrace : WordTrace (prefixWord ++ tailWord_4308911) baseStart_4308911 baseEnd_4308911 := by
    simpa [prefixWord, tailWord_4308911, baseEnd_4308911] using wordTrace_append hprefix tailTrace_4308911
  have hstable : (prefixWord ++ tailWord_4308911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308911).length < 2 ^ (prefixWord ++ tailWord_4308911).sum := by decide
  have hdescent : baseEnd_4308911 < baseStart_4308911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308921 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4308921 : Nat := 118140960795 + 4308921 * 2 ^ 59
def prefixEnd_4308921 : Nat := 4983230072969 + 3 ^ 40 * 4308921 * 2
def baseEnd_4308921 : Nat := 2212547575252041060471139

theorem tailTrace_4308921 : CollatzResearch.WordTrace tailWord_4308921 prefixEnd_4308921 2212547575252041060471139 := by
  unfold tailWord_4308921
  simp only [CollatzResearch.WordTrace]
  refine ⟨157159260022522596963510617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104772840015015064642340411 157159260022522596963510617)
  ·
    refine ⟨117869445016891947722632963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157159260022522596963510617 117869445016891947722632963)
    ·
      refine ⟨176804167525337921583949445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117869445016891947722632963 176804167525337921583949445)
      ·
        refine ⟨33150781411000860296990521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176804167525337921583949445 33150781411000860296990521)
        ·
          refine ⟨24863086058250645222742891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33150781411000860296990521 24863086058250645222742891)
          ·
            refine ⟨37294629087375967834114337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24863086058250645222742891 37294629087375967834114337)
            ·
              refine ⟨27970971815531975875585753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37294629087375967834114337 27970971815531975875585753)
              ·
                refine ⟨20978228861648981906689315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27970971815531975875585753 20978228861648981906689315)
                ·
                  refine ⟨31467343292473472860033973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20978228861648981906689315 31467343292473472860033973)
                  ·
                    refine ⟨2950063433669388080628185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31467343292473472860033973 2950063433669388080628185)
                    ·
                      refine ⟨2212547575252041060471139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950063433669388080628185 2212547575252041060471139)
                      ·
                        rfl

theorem cell23_4308921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4308921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308921 prefixEnd_4308921 := by exact prefixLift 4308921
  have htrace : WordTrace (prefixWord ++ tailWord_4308921) baseStart_4308921 baseEnd_4308921 := by
    simpa [prefixWord, tailWord_4308921, baseEnd_4308921] using wordTrace_append hprefix tailTrace_4308921
  have hstable : (prefixWord ++ tailWord_4308921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308921).length < 2 ^ (prefixWord ++ tailWord_4308921).sum := by decide
  have hdescent : baseEnd_4308921 < baseStart_4308921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308938 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_4308938 : Nat := 118140960795 + 4308938 * 2 ^ 59
def prefixEnd_4308938 : Nat := 4983230072969 + 3 ^ 40 * 4308938 * 2
def baseEnd_4308938 : Nat := 2212556304423167493958561

theorem tailTrace_4308938 : CollatzResearch.WordTrace tailWord_4308938 prefixEnd_4308938 2212556304423167493958561 := by
  unfold tailWord_4308938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39289970015865252216719867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104773253375640672577919645 39289970015865252216719867)
  ·
    refine ⟨58934955023797878325079801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39289970015865252216719867 58934955023797878325079801)
    ·
      refine ⟨44201216267848408743809851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58934955023797878325079801 44201216267848408743809851)
      ·
        refine ⟨66301824401772613115714777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44201216267848408743809851 66301824401772613115714777)
        ·
          refine ⟨49726368301329459836786083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66301824401772613115714777 49726368301329459836786083)
          ·
            refine ⟨74589552451994189755179125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49726368301329459836786083 74589552451994189755179125)
            ·
              refine ⟨6992770542374455289548043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74589552451994189755179125 6992770542374455289548043)
              ·
                refine ⟨10489155813561682934322065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992770542374455289548043 10489155813561682934322065)
                ·
                  refine ⟨7866866860171262200741549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10489155813561682934322065 7866866860171262200741549)
                  ·
                    refine ⟨2950075072564223325278081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7866866860171262200741549 2950075072564223325278081)
                    ·
                      refine ⟨2212556304423167493958561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950075072564223325278081 2212556304423167493958561)
                      ·
                        rfl

theorem cell23_4308938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_4308938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308938 prefixEnd_4308938 := by exact prefixLift 4308938
  have htrace : WordTrace (prefixWord ++ tailWord_4308938) baseStart_4308938 baseEnd_4308938 := by
    simpa [prefixWord, tailWord_4308938, baseEnd_4308938] using wordTrace_append hprefix tailTrace_4308938
  have hstable : (prefixWord ++ tailWord_4308938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308938).length < 2 ^ (prefixWord ++ tailWord_4308938).sum := by decide
  have hdescent : baseEnd_4308938 < baseStart_4308938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308944 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_4308944 : Nat := 118140960795 + 4308944 * 2 ^ 59
def prefixEnd_4308944 : Nat := 4983230072969 + 3 ^ 40 * 4308944 * 2
def baseEnd_4308944 : Nat := 737519795102364823494511

theorem tailTrace_4308944 : CollatzResearch.WordTrace tailWord_4308944 prefixEnd_4308944 737519795102364823494511 := by
  unfold tailWord_4308944
  simp only [CollatzResearch.WordTrace]
  refine ⟨78580049450719635945798943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104773399267626181261065257 78580049450719635945798943)
  ·
    refine ⟨117870074176079453918698415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78580049450719635945798943 117870074176079453918698415)
    ·
      refine ⟨176805111264119180878047623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117870074176079453918698415 176805111264119180878047623)
      ·
        refine ⟨265207666896178771317071435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176805111264119180878047623 265207666896178771317071435)
        ·
          refine ⟨397811500344268156975607153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265207666896178771317071435 397811500344268156975607153)
          ·
            refine ⟨298358625258201117731705365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397811500344268156975607153 298358625258201117731705365)
            ·
              refine ⟨13985560558978177393673689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 298358625258201117731705365 13985560558978177393673689)
              ·
                refine ⟨10489170419233633045255267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13985560558978177393673689 10489170419233633045255267)
                ·
                  refine ⟨15733755628850449567882901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10489170419233633045255267 15733755628850449567882901)
                  ·
                    refine ⟨737519795102364823494511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15733755628850449567882901 737519795102364823494511)
                    ·
                      rfl

theorem cell23_4308944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_4308944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308944 prefixEnd_4308944 := by exact prefixLift 4308944
  have htrace : WordTrace (prefixWord ++ tailWord_4308944) baseStart_4308944 baseEnd_4308944 := by
    simpa [prefixWord, tailWord_4308944, baseEnd_4308944] using wordTrace_append hprefix tailTrace_4308944
  have hstable : (prefixWord ++ tailWord_4308944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308944).length < 2 ^ (prefixWord ++ tailWord_4308944).sum := by decide
  have hdescent : baseEnd_4308944 < baseStart_4308944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308951 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_4308951 : Nat := 118140960795 + 4308951 * 2 ^ 59
def prefixEnd_4308951 : Nat := 4983230072969 + 3 ^ 40 * 4308951 * 2
def baseEnd_4308951 : Nat := 2212562979671675943096001

theorem tailTrace_4308951 : CollatzResearch.WordTrace tailWord_4308951 prefixEnd_4308951 2212562979671675943096001 := by
  unfold tailWord_4308951
  simp only [CollatzResearch.WordTrace]
  refine ⟨157160354212413912087102707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104773569474942608058068471 157160354212413912087102707)
  ·
    refine ⟨235740531318620868130654061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157160354212413912087102707 235740531318620868130654061)
    ·
      refine ⟨88402699244482825548995273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235740531318620868130654061 88402699244482825548995273)
      ·
        refine ⟨66302024433362119161746455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88402699244482825548995273 66302024433362119161746455)
        ·
          refine ⟨99453036650043178742619683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66302024433362119161746455 99453036650043178742619683)
          ·
            refine ⟨149179554975064768113929525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99453036650043178742619683 149179554975064768113929525)
            ·
              refine ⟨13985583278912322010680893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149179554975064768113929525 13985583278912322010680893)
              ·
                refine ⟨5244593729592120754005335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13985583278912322010680893 5244593729592120754005335)
                ·
                  refine ⟨7866890594388181131008003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244593729592120754005335 7866890594388181131008003)
                  ·
                    refine ⟨11800335891582271696512005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7866890594388181131008003 11800335891582271696512005)
                    ·
                      refine ⟨2212562979671675943096001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11800335891582271696512005 2212562979671675943096001)
                      ·
                        rfl

theorem cell23_4308951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_4308951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308951 prefixEnd_4308951 := by exact prefixLift 4308951
  have htrace : WordTrace (prefixWord ++ tailWord_4308951) baseStart_4308951 baseEnd_4308951 := by
    simpa [prefixWord, tailWord_4308951, baseEnd_4308951] using wordTrace_append hprefix tailTrace_4308951
  have hstable : (prefixWord ++ tailWord_4308951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308951).length < 2 ^ (prefixWord ++ tailWord_4308951).sum := by decide
  have hdescent : baseEnd_4308951 < baseStart_4308951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308962 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4308962 : Nat := 118140960795 + 4308962 * 2 ^ 59
def prefixEnd_4308962 : Nat := 4983230072969 + 3 ^ 40 * 4308962 * 2
def baseEnd_4308962 : Nat := 2212568627958875400058451

theorem tailTrace_4308962 : CollatzResearch.WordTrace tailWord_4308962 prefixEnd_4308962 2212568627958875400058451 := by
  unfold tailWord_4308962
  simp only [CollatzResearch.WordTrace]
  refine ⟨39290188853843515241438285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104773836943582707310502093 39290188853843515241438285)
  ·
    refine ⟨14733820820191318215539357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39290188853843515241438285 14733820820191318215539357)
    ·
      refine ⟨5525182807571744330827259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14733820820191318215539357 5525182807571744330827259)
      ·
        refine ⟨8287774211357616496240889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5525182807571744330827259 8287774211357616496240889)
        ·
          refine ⟨6215830658518212372180667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8287774211357616496240889 6215830658518212372180667)
          ·
            refine ⟨9323745987777318558271001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215830658518212372180667 9323745987777318558271001)
            ·
              refine ⟨6992809490832988918703251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9323745987777318558271001 6992809490832988918703251)
              ·
                refine ⟨10489214236249483378054877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992809490832988918703251 10489214236249483378054877)
                ·
                  refine ⟨3933455338593556266770579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10489214236249483378054877 3933455338593556266770579)
                  ·
                    refine ⟨5900183007890334400155869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933455338593556266770579 5900183007890334400155869)
                    ·
                      refine ⟨2212568627958875400058451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900183007890334400155869 2212568627958875400058451)
                      ·
                        rfl

theorem cell23_4308962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4308962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308962 prefixEnd_4308962 := by exact prefixLift 4308962
  have htrace : WordTrace (prefixWord ++ tailWord_4308962) baseStart_4308962 baseEnd_4308962 := by
    simpa [prefixWord, tailWord_4308962, baseEnd_4308962] using wordTrace_append hprefix tailTrace_4308962
  have hstable : (prefixWord ++ tailWord_4308962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308962).length < 2 ^ (prefixWord ++ tailWord_4308962).sum := by decide
  have hdescent : baseEnd_4308962 < baseStart_4308962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308964 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_4308964 : Nat := 118140960795 + 4308964 * 2 ^ 59
def prefixEnd_4308964 : Nat := 4983230072969 + 3 ^ 40 * 4308964 * 2
def baseEnd_4308964 : Nat := 2212569654920184392233441

theorem tailTrace_4308964 : CollatzResearch.WordTrace tailWord_4308964 prefixEnd_4308964 2212569654920184392233441 := by
  unfold tailWord_4308964
  simp only [CollatzResearch.WordTrace]
  refine ⟨78580414180683407653662973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104773885574244543538217297 78580414180683407653662973)
  ·
    refine ⟨29467655317756277870123615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78580414180683407653662973 29467655317756277870123615)
    ·
      refine ⟨44201482976634416805185423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29467655317756277870123615 44201482976634416805185423)
      ·
        refine ⟨66302224464951625207778135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44201482976634416805185423 66302224464951625207778135)
        ·
          refine ⟨99453336697427437811667203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66302224464951625207778135 99453336697427437811667203)
          ·
            refine ⟨149180005046141156717500805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99453336697427437811667203 149180005046141156717500805)
            ·
              refine ⟨27971250946151466884531401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149180005046141156717500805 27971250946151466884531401)
              ·
                refine ⟨20978438209613600163398551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27971250946151466884531401 20978438209613600163398551)
                ·
                  refine ⟨31467657314420400245097827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20978438209613600163398551 31467657314420400245097827)
                  ·
                    refine ⟨47201485971630600367646741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31467657314420400245097827 47201485971630600367646741)
                    ·
                      refine ⟨2212569654920184392233441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47201485971630600367646741 2212569654920184392233441)
                      ·
                        rfl

theorem cell23_4308964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_4308964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308964 prefixEnd_4308964 := by exact prefixLift 4308964
  have htrace : WordTrace (prefixWord ++ tailWord_4308964) baseStart_4308964 baseEnd_4308964 := by
    simpa [prefixWord, tailWord_4308964, baseEnd_4308964] using wordTrace_append hprefix tailTrace_4308964
  have hstable : (prefixWord ++ tailWord_4308964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308964).length < 2 ^ (prefixWord ++ tailWord_4308964).sum := by decide
  have hdescent : baseEnd_4308964 < baseStart_4308964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308988 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_4308988 : Nat := 118140960795 + 4308988 * 2 ^ 59
def prefixEnd_4308988 : Nat := 4983230072969 + 3 ^ 40 * 4308988 * 2
def baseEnd_4308988 : Nat := 2212581978455892298333331

theorem tailTrace_4308988 : CollatzResearch.WordTrace tailWord_4308988 prefixEnd_4308988 2212581978455892298333331 := by
  unfold tailWord_4308988
  simp only [CollatzResearch.WordTrace]
  refine ⟨78580851856639933703099809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104774469142186578270799745 78580851856639933703099809)
  ·
    refine ⟨58935638892479950277324857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78580851856639933703099809 58935638892479950277324857)
    ·
      refine ⟨44201729169359962707993643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58935638892479950277324857 44201729169359962707993643)
      ·
        refine ⟨66302593754039944061990465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44201729169359962707993643 66302593754039944061990465)
        ·
          refine ⟨49726945315529958046492849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66302593754039944061990465 49726945315529958046492849)
          ·
            refine ⟨37295208986647468534869637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49726945315529958046492849 37295208986647468534869637)
            ·
              refine ⟨6992851684996400350288057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37295208986647468534869637 6992851684996400350288057)
              ·
                refine ⟨5244638763747300262716043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6992851684996400350288057 5244638763747300262716043)
                ·
                  refine ⟨7866958145620950394074065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244638763747300262716043 7866958145620950394074065)
                  ·
                    refine ⟨5900218609215712795555549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7866958145620950394074065 5900218609215712795555549)
                    ·
                      refine ⟨2212581978455892298333331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900218609215712795555549 2212581978455892298333331)
                      ·
                        rfl

theorem cell23_4308988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_4308988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308988 prefixEnd_4308988 := by exact prefixLift 4308988
  have htrace : WordTrace (prefixWord ++ tailWord_4308988) baseStart_4308988 baseEnd_4308988 := by
    simpa [prefixWord, tailWord_4308988, baseEnd_4308988] using wordTrace_append hprefix tailTrace_4308988
  have hstable : (prefixWord ++ tailWord_4308988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308988).length < 2 ^ (prefixWord ++ tailWord_4308988).sum := by decide
  have hdescent : baseEnd_4308988 < baseStart_4308988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4308996 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4308996 : Nat := 118140960795 + 4308996 * 2 ^ 59
def prefixEnd_4308996 : Nat := 4983230072969 + 3 ^ 40 * 4308996 * 2
def baseEnd_4308996 : Nat := 2212586086301128267033295

theorem tailTrace_4308996 : CollatzResearch.WordTrace tailWord_4308996 prefixEnd_4308996 2212586086301128267033295 := by
  unfold tailWord_4308996
  simp only [CollatzResearch.WordTrace]
  refine ⟨78580997748625442386245421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104774663664833923181660561 78580997748625442386245421)
  ·
    refine ⟨29467874155734540894842033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78580997748625442386245421 29467874155734540894842033)
    ·
      refine ⟨22100905616800905671131525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29467874155734540894842033 22100905616800905671131525)
      ·
        refine ⟨4143919803150169813337161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22100905616800905671131525 4143919803150169813337161)
        ·
          refine ⟨3107939852362627360002871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4143919803150169813337161 3107939852362627360002871)
          ·
            refine ⟨4661909778543941040004307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107939852362627360002871 4661909778543941040004307)
            ·
              refine ⟨6992864667815911560006461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661909778543941040004307 6992864667815911560006461)
              ·
                refine ⟨2622324250430966835002423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6992864667815911560006461 2622324250430966835002423)
                ·
                  refine ⟨3933486375646450252503635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622324250430966835002423 3933486375646450252503635)
                  ·
                    refine ⟨5900229563469675378755453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933486375646450252503635 5900229563469675378755453)
                    ·
                      refine ⟨2212586086301128267033295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900229563469675378755453 2212586086301128267033295)
                      ·
                        rfl

theorem cell23_4308996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4308996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4308996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4308996 prefixEnd_4308996 := by exact prefixLift 4308996
  have htrace : WordTrace (prefixWord ++ tailWord_4308996) baseStart_4308996 baseEnd_4308996 := by
    simpa [prefixWord, tailWord_4308996, baseEnd_4308996] using wordTrace_append hprefix tailTrace_4308996
  have hstable : (prefixWord ++ tailWord_4308996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4308996).length < 2 ^ (prefixWord ++ tailWord_4308996).sum := by decide
  have hdescent : baseEnd_4308996 < baseStart_4308996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4308996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309018 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_4309018 : Nat := 118140960795 + 4309018 * 2 ^ 59
def prefixEnd_4309018 : Nat := 4983230072969 + 3 ^ 40 * 4309018 * 2
def baseEnd_4309018 : Nat := 2212597382875527180958193

theorem tailTrace_4309018 : CollatzResearch.WordTrace tailWord_4309018 prefixEnd_4309018 2212597382875527180958193 := by
  unfold tailWord_4309018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39290699475792795632447927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104775198602114121686527805 39290699475792795632447927)
  ·
    refine ⟨58936049213689193448671891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39290699475792795632447927 58936049213689193448671891)
    ·
      refine ⟨88404073820533790173007837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58936049213689193448671891 88404073820533790173007837)
      ·
        refine ⟨33151527682700171314877939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88404073820533790173007837 33151527682700171314877939)
        ·
          refine ⟨49727291524050256972316909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33151527682700171314877939 49727291524050256972316909)
          ·
            refine ⟨18647734321518846364618841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49727291524050256972316909 18647734321518846364618841)
            ·
              refine ⟨13985800741139134773464131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18647734321518846364618841 13985800741139134773464131)
              ·
                refine ⟨20978701111708702160196197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13985800741139134773464131 20978701111708702160196197)
                ·
                  refine ⟨3933506458445381655036787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20978701111708702160196197 3933506458445381655036787)
                  ·
                    refine ⟨5900259687668072482555181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3933506458445381655036787 5900259687668072482555181)
                    ·
                      refine ⟨2212597382875527180958193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900259687668072482555181 2212597382875527180958193)
                      ·
                        rfl

theorem cell23_4309018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_4309018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309018 prefixEnd_4309018 := by exact prefixLift 4309018
  have htrace : WordTrace (prefixWord ++ tailWord_4309018) baseStart_4309018 baseEnd_4309018 := by
    simpa [prefixWord, tailWord_4309018, baseEnd_4309018] using wordTrace_append hprefix tailTrace_4309018
  have hstable : (prefixWord ++ tailWord_4309018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309018).length < 2 ^ (prefixWord ++ tailWord_4309018).sum := by decide
  have hdescent : baseEnd_4309018 < baseStart_4309018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309045 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_4309045 : Nat := 118140960795 + 4309045 * 2 ^ 59
def prefixEnd_4309045 : Nat := 4983230072969 + 3 ^ 40 * 4309045 * 2
def baseEnd_4309045 : Nat := 2212611246853198575320569

theorem tailTrace_4309045 : CollatzResearch.WordTrace tailWord_4309045 prefixEnd_4309045 2212611246853198575320569 := by
  unfold tailWord_4309045
  simp only [CollatzResearch.WordTrace]
  refine ⟨157163782674073366141024589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104775855116048910760683059 157163782674073366141024589)
  ·
    refine ⟨58936418502777512302884221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157163782674073366141024589 58936418502777512302884221)
    ·
      refine ⟨22101156938541567113581583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58936418502777512302884221 22101156938541567113581583)
      ·
        refine ⟨33151735407812350670372375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22101156938541567113581583 33151735407812350670372375)
        ·
          refine ⟨49727603111718526005558563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33151735407812350670372375 49727603111718526005558563)
          ·
            refine ⟨74591404667577789008337845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49727603111718526005558563 74591404667577789008337845)
            ·
              refine ⟨6992944187585417719531673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74591404667577789008337845 6992944187585417719531673)
              ·
                refine ⟨5244708140689063289648755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6992944187585417719531673 5244708140689063289648755)
                ·
                  refine ⟨7867062211033594934473133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244708140689063289648755 7867062211033594934473133)
                  ·
                    refine ⟨2950148329137598100427425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7867062211033594934473133 2950148329137598100427425)
                    ·
                      refine ⟨2212611246853198575320569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950148329137598100427425 2212611246853198575320569)
                      ·
                        rfl

theorem cell23_4309045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_4309045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309045 prefixEnd_4309045 := by exact prefixLift 4309045
  have htrace : WordTrace (prefixWord ++ tailWord_4309045) baseStart_4309045 baseEnd_4309045 := by
    simpa [prefixWord, tailWord_4309045, baseEnd_4309045] using wordTrace_append hprefix tailTrace_4309045
  have hstable : (prefixWord ++ tailWord_4309045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309045).length < 2 ^ (prefixWord ++ tailWord_4309045).sum := by decide
  have hdescent : baseEnd_4309045 < baseStart_4309045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309064 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 11]
def baseStart_4309064 : Nat := 118140960795 + 4309064 * 2 ^ 59
def prefixEnd_4309064 : Nat := 4983230072969 + 3 ^ 40 * 4309064 * 2
def baseEnd_4309064 : Nat := 245846778109514888998109

theorem tailTrace_4309064 : CollatzResearch.WordTrace tailWord_4309064 prefixEnd_4309064 245846778109514888998109 := by
  unfold tailWord_4309064
  simp only [CollatzResearch.WordTrace]
  refine ⟨78582237830502266192983123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104776317107336354923977497 78582237830502266192983123)
  ·
    refine ⟨117873356745753399289474685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78582237830502266192983123 117873356745753399289474685)
    ·
      refine ⟨44202508779657524733553007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117873356745753399289474685 44202508779657524733553007)
      ·
        refine ⟨66303763169486287100329511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44202508779657524733553007 66303763169486287100329511)
        ·
          refine ⟨99455644754229430650494267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66303763169486287100329511 99455644754229430650494267)
          ·
            refine ⟨149183467131344145975741401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99455644754229430650494267 149183467131344145975741401)
            ·
              refine ⟨111887600348508109481806051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149183467131344145975741401 111887600348508109481806051)
              ·
                refine ⟨167831400522762164222709077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111887600348508109481806051 167831400522762164222709077)
                ·
                  refine ⟨245846778109514888998109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 167831400522762164222709077 245846778109514888998109)
                  ·
                    rfl

theorem cell23_4309064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_4309064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309064 prefixEnd_4309064 := by exact prefixLift 4309064
  have htrace : WordTrace (prefixWord ++ tailWord_4309064) baseStart_4309064 baseEnd_4309064 := by
    simpa [prefixWord, tailWord_4309064, baseEnd_4309064] using wordTrace_append hprefix tailTrace_4309064
  have hstable : (prefixWord ++ tailWord_4309064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309064).length < 2 ^ (prefixWord ++ tailWord_4309064).sum := by decide
  have hdescent : baseEnd_4309064 < baseStart_4309064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309091 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3]
def baseStart_4309091 : Nat := 118140960795 + 4309091 * 2 ^ 59
def prefixEnd_4309091 : Nat := 4983230072969 + 3 ^ 40 * 4309091 * 2
def baseEnd_4309091 : Nat := 2212634866963305395345357

theorem tailTrace_4309091 : CollatzResearch.WordTrace tailWord_4309091 prefixEnd_4309091 2212634866963305395345357 := by
  unfold tailWord_4309091
  simp only [CollatzResearch.WordTrace]
  refine ⟨157165460431906715997199127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104776973621271143998132751 157165460431906715997199127)
  ·
    refine ⟨235748190647860073995798691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157165460431906715997199127 235748190647860073995798691)
    ·
      refine ⟨353622285971790110993698037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235748190647860073995798691 353622285971790110993698037)
      ·
        refine ⟨33152089309855322905659191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 353622285971790110993698037 33152089309855322905659191)
        ·
          refine ⟨49728133964782984358488787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33152089309855322905659191 49728133964782984358488787)
          ·
            refine ⟨74592200947174476537733181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49728133964782984358488787 74592200947174476537733181)
            ·
              refine ⟨27972075355190428701649943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74592200947174476537733181 27972075355190428701649943)
              ·
                refine ⟨41958113032785643052474915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27972075355190428701649943 41958113032785643052474915)
                ·
                  refine ⟨62937169549178464578712373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41958113032785643052474915 62937169549178464578712373)
                  ·
                    refine ⟨5900359645235481054254285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62937169549178464578712373 5900359645235481054254285)
                    ·
                      refine ⟨2212634866963305395345357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900359645235481054254285 2212634866963305395345357)
                      ·
                        rfl

theorem cell23_4309091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_4309091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309091 prefixEnd_4309091 := by exact prefixLift 4309091
  have htrace : WordTrace (prefixWord ++ tailWord_4309091) baseStart_4309091 baseEnd_4309091 := by
    simpa [prefixWord, tailWord_4309091, baseEnd_4309091] using wordTrace_append hprefix tailTrace_4309091
  have hstable : (prefixWord ++ tailWord_4309091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309091).length < 2 ^ (prefixWord ++ tailWord_4309091).sum := by decide
  have hdescent : baseEnd_4309091 < baseStart_4309091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309098 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_4309098 : Nat := 118140960795 + 4309098 * 2 ^ 59
def prefixEnd_4309098 : Nat := 4983230072969 + 3 ^ 40 * 4309098 * 2
def baseEnd_4309098 : Nat := 245848717925320763106425

theorem tailTrace_4309098 : CollatzResearch.WordTrace tailWord_4309098 prefixEnd_4309098 245848717925320763106425 := by
  unfold tailWord_4309098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39291428935720339048175987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104777143828587570795135965 39291428935720339048175987)
  ·
    refine ⟨58937143403580508572263981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39291428935720339048175987 58937143403580508572263981)
    ·
      refine ⟨22101428776342690714598993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58937143403580508572263981 22101428776342690714598993)
      ·
        refine ⟨16576071582257018035949245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22101428776342690714598993 16576071582257018035949245)
        ·
          refine ⟨6216026843346381763480967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16576071582257018035949245 6216026843346381763480967)
          ·
            refine ⟨9324040265019572645221451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216026843346381763480967 9324040265019572645221451)
            ·
              refine ⟨13986060397529358967832177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9324040265019572645221451 13986060397529358967832177)
              ·
                refine ⟨10489545298147019225874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13986060397529358967832177 10489545298147019225874133)
                ·
                  refine ⟨245848717925320763106425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10489545298147019225874133 245848717925320763106425)
                  ·
                    rfl

theorem cell23_4309098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_4309098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309098 prefixEnd_4309098 := by exact prefixLift 4309098
  have htrace : WordTrace (prefixWord ++ tailWord_4309098) baseStart_4309098 baseEnd_4309098 := by
    simpa [prefixWord, tailWord_4309098, baseEnd_4309098] using wordTrace_append hprefix tailTrace_4309098
  have hstable : (prefixWord ++ tailWord_4309098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309098).length < 2 ^ (prefixWord ++ tailWord_4309098).sum := by decide
  have hdescent : baseEnd_4309098 < baseStart_4309098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309111 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 7]
def baseStart_4309111 : Nat := 118140960795 + 4309111 * 2 ^ 59
def prefixEnd_4309111 : Nat := 4983230072969 + 3 ^ 40 * 4309111 * 2
def baseEnd_4309111 : Nat := 737548378858798439031755

theorem tailTrace_4309111 : CollatzResearch.WordTrace tailWord_4309111 prefixEnd_4309111 737548378858798439031755 := by
  unfold tailWord_4309111
  simp only [CollatzResearch.WordTrace]
  refine ⟨157166189891834259412927187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104777459927889506275284791 157166189891834259412927187)
  ·
    refine ⟨235749284837751389119390781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157166189891834259412927187 235749284837751389119390781)
    ·
      refine ⟨88405981814156770919771543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235749284837751389119390781 88405981814156770919771543)
      ·
        refine ⟨132608972721235156379657315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88405981814156770919771543 132608972721235156379657315)
        ·
          refine ⟨198913459081852734569485973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132608972721235156379657315 198913459081852734569485973)
          ·
            refine ⟨9324068394461846932944655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 198913459081852734569485973 9324068394461846932944655)
            ·
              refine ⟨13986102591692770399416983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9324068394461846932944655 13986102591692770399416983)
              ·
                refine ⟨20979153887539155599125475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13986102591692770399416983 20979153887539155599125475)
                ·
                  refine ⟨31468730831308733398688213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20979153887539155599125475 31468730831308733398688213)
                  ·
                    refine ⟨737548378858798439031755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31468730831308733398688213 737548378858798439031755)
                    ·
                      rfl

theorem cell23_4309111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_4309111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309111 prefixEnd_4309111 := by exact prefixLift 4309111
  have htrace : WordTrace (prefixWord ++ tailWord_4309111) baseStart_4309111 baseEnd_4309111 := by
    simpa [prefixWord, tailWord_4309111, baseEnd_4309111] using wordTrace_append hprefix tailTrace_4309111
  have hstable : (prefixWord ++ tailWord_4309111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309111).length < 2 ^ (prefixWord ++ tailWord_4309111).sum := by decide
  have hdescent : baseEnd_4309111 < baseStart_4309111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309166 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_4309166 : Nat := 118140960795 + 4309166 * 2 ^ 59
def prefixEnd_4309166 : Nat := 4983230072969 + 3 ^ 40 * 4309166 * 2
def baseEnd_4309166 : Nat := 245852597556932511323057

theorem tailTrace_4309166 : CollatzResearch.WordTrace tailWord_4309166 prefixEnd_4309166 245852597556932511323057 := by
  unfold tailWord_4309166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19646024488329375475772419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104778797271090002537452901 19646024488329375475772419)
  ·
    refine ⟨29469036732494063213658629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19646024488329375475772419 29469036732494063213658629)
    ·
      refine ⟨5525444387342636852560993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29469036732494063213658629 5525444387342636852560993)
      ·
        refine ⟨4144083290506977639420745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5525444387342636852560993 4144083290506977639420745)
        ·
          refine ⟨3108062467880233229565559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144083290506977639420745 3108062467880233229565559)
          ·
            refine ⟨4662093701820349844348339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108062467880233229565559 4662093701820349844348339)
            ·
              refine ⟨6993140552730524766522509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662093701820349844348339 6993140552730524766522509)
              ·
                refine ⟨2622427707273946787445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6993140552730524766522509 2622427707273946787445941)
                ·
                  refine ⟨245852597556932511323057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2622427707273946787445941 245852597556932511323057)
                  ·
                    rfl

theorem cell23_4309166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_4309166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309166 prefixEnd_4309166 := by exact prefixLift 4309166
  have htrace : WordTrace (prefixWord ++ tailWord_4309166) baseStart_4309166 baseEnd_4309166 := by
    simpa [prefixWord, tailWord_4309166, baseEnd_4309166] using wordTrace_append hprefix tailTrace_4309166
  have hstable : (prefixWord ++ tailWord_4309166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309166).length < 2 ^ (prefixWord ++ tailWord_4309166).sum := by decide
  have hdescent : baseEnd_4309166 < baseStart_4309166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309188 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 8]
def baseStart_4309188 : Nat := 118140960795 + 4309188 * 2 ^ 59
def prefixEnd_4309188 : Nat := 4983230072969 + 3 ^ 40 * 4309188 * 2
def baseEnd_4309188 : Nat := 245853852731865723981379

theorem tailTrace_4309188 : CollatzResearch.WordTrace tailWord_4309188 prefixEnd_4309188 245853852731865723981379 := by
  unfold tailWord_4309188
  simp only [CollatzResearch.WordTrace]
  refine ⟨78584499156277650781740109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104779332208370201042320145 78584499156277650781740109)
  ·
    refine ⟨29469187183604119043152541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78584499156277650781740109 29469187183604119043152541)
    ·
      refine ⟨11050945193851544641182203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29469187183604119043152541 11050945193851544641182203)
      ·
        refine ⟨16576417790777316961773305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11050945193851544641182203 16576417790777316961773305)
        ·
          refine ⟨12432313343082987721329979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16576417790777316961773305 12432313343082987721329979)
          ·
            refine ⟨18648470014624481581994969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12432313343082987721329979 18648470014624481581994969)
            ·
              refine ⟨13986352510968361186496227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18648470014624481581994969 13986352510968361186496227)
              ·
                refine ⟨20979528766452541779744341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13986352510968361186496227 20979528766452541779744341)
                ·
                  refine ⟨245853852731865723981379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20979528766452541779744341 245853852731865723981379)
                  ·
                    rfl

theorem cell23_4309188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_4309188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309188 prefixEnd_4309188 := by exact prefixLift 4309188
  have htrace : WordTrace (prefixWord ++ tailWord_4309188) baseStart_4309188 baseEnd_4309188 := by
    simpa [prefixWord, tailWord_4309188, baseEnd_4309188] using wordTrace_append hprefix tailTrace_4309188
  have hstable : (prefixWord ++ tailWord_4309188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309188).length < 2 ^ (prefixWord ++ tailWord_4309188).sum := by decide
  have hdescent : baseEnd_4309188 < baseStart_4309188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309205 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 6]
def baseStart_4309205 : Nat := 118140960795 + 4309205 * 2 ^ 59
def prefixEnd_4309205 : Nat := 4983230072969 + 3 ^ 40 * 4309205 * 2
def baseEnd_4309205 : Nat := 245854822639768661035537

theorem tailTrace_4309205 : CollatzResearch.WordTrace tailWord_4309205 prefixEnd_4309205 245854822639768661035537 := by
  unfold tailWord_4309205
  simp only [CollatzResearch.WordTrace]
  refine ⟨157169618353493713466849069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104779745568995808977899379 157169618353493713466849069)
  ·
    refine ⟨58938606882560142550068401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157169618353493713466849069 58938606882560142550068401)
    ·
      refine ⟨44203955161920106912551301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58938606882560142550068401 44203955161920106912551301)
      ·
        refine ⟨8288241592860020046103369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44203955161920106912551301 8288241592860020046103369)
        ·
          refine ⟨6216181194645015034577527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8288241592860020046103369 6216181194645015034577527)
          ·
            refine ⟨9324271791967522551866291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216181194645015034577527 9324271791967522551866291)
            ·
              refine ⟨13986407687951283827799437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9324271791967522551866291 13986407687951283827799437)
              ·
                refine ⟨5244902882981731435424789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13986407687951283827799437 5244902882981731435424789)
                ·
                  refine ⟨245854822639768661035537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5244902882981731435424789 245854822639768661035537)
                  ·
                    rfl

theorem cell23_4309205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_4309205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309205 prefixEnd_4309205 := by exact prefixLift 4309205
  have htrace : WordTrace (prefixWord ++ tailWord_4309205) baseStart_4309205 baseEnd_4309205 := by
    simpa [prefixWord, tailWord_4309205, baseEnd_4309205] using wordTrace_append hprefix tailTrace_4309205
  have hstable : (prefixWord ++ tailWord_4309205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309205).length < 2 ^ (prefixWord ++ tailWord_4309205).sum := by decide
  have hdescent : baseEnd_4309205 < baseStart_4309205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309235 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 1, 5]
def baseStart_4309235 : Nat := 118140960795 + 4309235 * 2 ^ 59
def prefixEnd_4309235 : Nat := 4983230072969 + 3 ^ 40 * 4309235 * 2
def baseEnd_4309235 : Nat := 737569602725850943981565

theorem tailTrace_4309235 : CollatzResearch.WordTrace tailWord_4309235 prefixEnd_4309235 737569602725850943981565 := by
  unfold tailWord_4309235
  simp only [CollatzResearch.WordTrace]
  refine ⟨157170712543385028590441159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104780475028923352393627439 157170712543385028590441159)
  ·
    refine ⟨235756068815077542885661739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157170712543385028590441159 235756068815077542885661739)
    ·
      refine ⟨353634103222616314328492609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235756068815077542885661739 353634103222616314328492609)
      ·
        refine ⟨265225577416962235746369457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353634103222616314328492609 265225577416962235746369457)
        ·
          refine ⟨198919183062721676809777093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265225577416962235746369457 198919183062721676809777093)
          ·
            refine ⟨37297346824260314401833205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198919183062721676809777093 37297346824260314401833205)
            ·
              refine ⟨3496626264774404475171863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37297346824260314401833205 3496626264774404475171863)
              ·
                refine ⟨5244939397161606712757795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496626264774404475171863 5244939397161606712757795)
                ·
                  refine ⟨7867409095742410069136693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244939397161606712757795 7867409095742410069136693)
                  ·
                    refine ⟨737569602725850943981565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7867409095742410069136693 737569602725850943981565)
                    ·
                      rfl

theorem cell23_4309235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 5].length) (baseStart_4309235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309235 prefixEnd_4309235 := by exact prefixLift 4309235
  have htrace : WordTrace (prefixWord ++ tailWord_4309235) baseStart_4309235 baseEnd_4309235 := by
    simpa [prefixWord, tailWord_4309235, baseEnd_4309235] using wordTrace_append hprefix tailTrace_4309235
  have hstable : (prefixWord ++ tailWord_4309235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309235).length < 2 ^ (prefixWord ++ tailWord_4309235).sum := by decide
  have hdescent : baseEnd_4309235 < baseStart_4309235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309248 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_4309248 : Nat := 118140960795 + 4309248 * 2 ^ 59
def prefixEnd_4309248 : Nat := 4983230072969 + 3 ^ 40 * 4309248 * 2
def baseEnd_4309248 : Nat := 737571827808687093694045

theorem tailTrace_4309248 : CollatzResearch.WordTrace tailWord_4309248 prefixEnd_4309248 737571827808687093694045 := by
  unfold tailWord_4309248
  simp only [CollatzResearch.WordTrace]
  refine ⟨78585593346168965905332199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104780791128225287873776265 78585593346168965905332199)
  ·
    refine ⟨117878390019253448857998299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78585593346168965905332199 117878390019253448857998299)
    ·
      refine ⟨176817585028880173286997449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117878390019253448857998299 176817585028880173286997449)
      ·
        refine ⟨132613188771660129965248087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176817585028880173286997449 132613188771660129965248087)
        ·
          refine ⟨198919783157490194947872131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132613188771660129965248087 198919783157490194947872131)
          ·
            refine ⟨298379674736235292421808197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198919783157490194947872131 298379674736235292421808197)
            ·
              refine ⟨55946189013044117329089037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298379674736235292421808197 55946189013044117329089037)
              ·
                refine ⟨20979820879891543998408389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55946189013044117329089037 20979820879891543998408389)
                ·
                  refine ⟨3933716414979664499701573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20979820879891543998408389 3933716414979664499701573)
                  ·
                    refine ⟨737571827808687093694045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933716414979664499701573 737571827808687093694045)
                    ·
                      rfl

theorem cell23_4309248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_4309248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309248 prefixEnd_4309248 := by exact prefixLift 4309248
  have htrace : WordTrace (prefixWord ++ tailWord_4309248) baseStart_4309248 baseEnd_4309248 := by
    simpa [prefixWord, tailWord_4309248, baseEnd_4309248] using wordTrace_append hprefix tailTrace_4309248
  have hstable : (prefixWord ++ tailWord_4309248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309248).length < 2 ^ (prefixWord ++ tailWord_4309248).sum := by decide
  have hdescent : baseEnd_4309248 < baseStart_4309248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309258 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4309258 : Nat := 118140960795 + 4309258 * 2 ^ 59
def prefixEnd_4309258 : Nat := 4983230072969 + 3 ^ 40 * 4309258 * 2
def baseEnd_4309258 : Nat := 2212720618232606241957089

theorem tailTrace_4309258 : CollatzResearch.WordTrace tailWord_4309258 prefixEnd_4309258 2212720618232606241957089 := by
  unfold tailWord_4309258
  simp only [CollatzResearch.WordTrace]
  refine ⟨39292887855575425879632107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104781034281534469012352285 39292887855575425879632107)
  ·
    refine ⟨58939331783363138819448161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39292887855575425879632107 58939331783363138819448161)
    ·
      refine ⟨44204498837522354114586121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58939331783363138819448161 44204498837522354114586121)
      ·
        refine ⟨33153374128141765585939591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44204498837522354114586121 33153374128141765585939591)
        ·
          refine ⟨49730061192212648378909387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33153374128141765585939591 49730061192212648378909387)
          ·
            refine ⟨74595091788318972568364081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49730061192212648378909387 74595091788318972568364081)
            ·
              refine ⟨55946318841239229426273061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74595091788318972568364081 55946318841239229426273061)
              ·
                refine ⟨10489934782732355517426199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55946318841239229426273061 10489934782732355517426199)
                ·
                  refine ⟨15734902174098533276139299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10489934782732355517426199 15734902174098533276139299)
                  ·
                    refine ⟨23602353261147799914208949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15734902174098533276139299 23602353261147799914208949)
                    ·
                      refine ⟨2212720618232606241957089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23602353261147799914208949 2212720618232606241957089)
                      ·
                        rfl

theorem cell23_4309258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4309258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309258 prefixEnd_4309258 := by exact prefixLift 4309258
  have htrace : WordTrace (prefixWord ++ tailWord_4309258) baseStart_4309258 baseEnd_4309258 := by
    simpa [prefixWord, tailWord_4309258, baseEnd_4309258] using wordTrace_append hprefix tailTrace_4309258
  have hstable : (prefixWord ++ tailWord_4309258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309258).length < 2 ^ (prefixWord ++ tailWord_4309258).sum := by decide
  have hdescent : baseEnd_4309258 < baseStart_4309258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309265 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_4309265 : Nat := 118140960795 + 4309265 * 2 ^ 59
def prefixEnd_4309265 : Nat := 4983230072969 + 3 ^ 40 * 4309265 * 2
def baseEnd_4309265 : Nat := 737574737532395904856519

theorem tailTrace_4309265 : CollatzResearch.WordTrace tailWord_4309265 prefixEnd_4309265 737574737532395904856519 := by
  unfold tailWord_4309265
  simp only [CollatzResearch.WordTrace]
  refine ⟨157171806733276343714033249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104781204488850895809355499 157171806733276343714033249)
  ·
    refine ⟨117878855049957257785524937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157171806733276343714033249 117878855049957257785524937)
    ·
      refine ⟨88409141287467943339143703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117878855049957257785524937 88409141287467943339143703)
      ·
        refine ⟨132613711931201915008715555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88409141287467943339143703 132613711931201915008715555)
        ·
          refine ⟨198920567896802872513073333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132613711931201915008715555 198920567896802872513073333)
          ·
            refine ⟨18648803240325269298100625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198920567896802872513073333 18648803240325269298100625)
            ·
              refine ⟨13986602430243951973575469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18648803240325269298100625 13986602430243951973575469)
              ·
                refine ⟨5244975911341481990090801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13986602430243951973575469 5244975911341481990090801)
                ·
                  refine ⟨3933731933506111492568101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5244975911341481990090801 3933731933506111492568101)
                  ·
                    refine ⟨737574737532395904856519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933731933506111492568101 737574737532395904856519)
                    ·
                      rfl

theorem cell23_4309265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_4309265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309265 prefixEnd_4309265 := by exact prefixLift 4309265
  have htrace : WordTrace (prefixWord ++ tailWord_4309265) baseStart_4309265 baseEnd_4309265 := by
    simpa [prefixWord, tailWord_4309265, baseEnd_4309265] using wordTrace_append hprefix tailTrace_4309265
  have hstable : (prefixWord ++ tailWord_4309265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309265).length < 2 ^ (prefixWord ++ tailWord_4309265).sum := by decide
  have hdescent : baseEnd_4309265 < baseStart_4309265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309272 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_4309272 : Nat := 118140960795 + 4309272 * 2 ^ 59
def prefixEnd_4309272 : Nat := 4983230072969 + 3 ^ 40 * 4309272 * 2
def baseEnd_4309272 : Nat := 2212727806961769187182025

theorem tailTrace_4309272 : CollatzResearch.WordTrace tailWord_4309272 prefixEnd_4309272 2212727806961769187182025 := by
  unfold tailWord_4309272
  simp only [CollatzResearch.WordTrace]
  refine ⟨78586031022125491954769035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104781374696167322606358713 78586031022125491954769035)
  ·
    refine ⟨117879046533188237932153553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78586031022125491954769035 117879046533188237932153553)
    ·
      refine ⟨88409284899891178449115165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117879046533188237932153553 88409284899891178449115165)
      ·
        refine ⟨33153481837459191918418187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88409284899891178449115165 33153481837459191918418187)
        ·
          refine ⟨49730222756188787877627281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33153481837459191918418187 49730222756188787877627281)
          ·
            refine ⟨37297667067141590908220461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49730222756188787877627281 37297667067141590908220461)
            ·
              refine ⟨13986625150178096590582673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37297667067141590908220461 13986625150178096590582673)
              ·
                refine ⟨10489968862633572442937005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13986625150178096590582673 10489968862633572442937005)
                ·
                  refine ⟨3933738323487589666101377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10489968862633572442937005 3933738323487589666101377)
                  ·
                    refine ⟨2950303742615692249576033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3933738323487589666101377 2950303742615692249576033)
                    ·
                      refine ⟨2212727806961769187182025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950303742615692249576033 2212727806961769187182025)
                      ·
                        rfl

theorem cell23_4309272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_4309272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309272 prefixEnd_4309272 := by exact prefixLift 4309272
  have htrace : WordTrace (prefixWord ++ tailWord_4309272) baseStart_4309272 baseEnd_4309272 := by
    simpa [prefixWord, tailWord_4309272, baseEnd_4309272] using wordTrace_append hprefix tailTrace_4309272
  have hstable : (prefixWord ++ tailWord_4309272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309272).length < 2 ^ (prefixWord ++ tailWord_4309272).sum := by decide
  have hdescent : baseEnd_4309272 < baseStart_4309272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309292 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_4309292 : Nat := 118140960795 + 4309292 * 2 ^ 59
def prefixEnd_4309292 : Nat := 4983230072969 + 3 ^ 40 * 4309292 * 2
def baseEnd_4309292 : Nat := 2212738076574859108931933

theorem tailTrace_4309292 : CollatzResearch.WordTrace tailWord_4309292 prefixEnd_4309292 2212738076574859108931933 := by
  unfold tailWord_4309292
  simp only [CollatzResearch.WordTrace]
  refine ⟨78586395752089263662633065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104781861002785684883510753 78586395752089263662633065)
  ·
    refine ⟨58939796814066947746974799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78586395752089263662633065 58939796814066947746974799)
    ·
      refine ⟨88409695221100421620462199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58939796814066947746974799 88409695221100421620462199)
      ·
        refine ⟨132614542831650632430693299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88409695221100421620462199 132614542831650632430693299)
        ·
          refine ⟨198921814247475948646039949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132614542831650632430693299 198921814247475948646039949)
          ·
            refine ⟨74595680342803480742264981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198921814247475948646039949 74595680342803480742264981)
            ·
              refine ⟨3496672516068913159793671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74595680342803480742264981 3496672516068913159793671)
              ·
                refine ⟨5245008774103369739690507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496672516068913159793671 5245008774103369739690507)
                ·
                  refine ⟨7867513161155054609535761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245008774103369739690507 7867513161155054609535761)
                  ·
                    refine ⟨5900634870866290957151821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7867513161155054609535761 5900634870866290957151821)
                    ·
                      refine ⟨2212738076574859108931933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5900634870866290957151821 2212738076574859108931933)
                      ·
                        rfl

theorem cell23_4309292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_4309292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309292 prefixEnd_4309292 := by exact prefixLift 4309292
  have htrace : WordTrace (prefixWord ++ tailWord_4309292) baseStart_4309292 baseEnd_4309292 := by
    simpa [prefixWord, tailWord_4309292, baseEnd_4309292] using wordTrace_append hprefix tailTrace_4309292
  have hstable : (prefixWord ++ tailWord_4309292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309292).length < 2 ^ (prefixWord ++ tailWord_4309292).sum := by decide
  have hdescent : baseEnd_4309292 < baseStart_4309292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309315 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 5, 3, 2]
def baseStart_4309315 : Nat := 118140960795 + 4309315 * 2 ^ 59
def prefixEnd_4309315 : Nat := 4983230072969 + 3 ^ 40 * 4309315 * 2
def baseEnd_4309315 : Nat := 2212749886629912518944327

theorem tailTrace_4309315 : CollatzResearch.WordTrace tailWord_4309315 prefixEnd_4309315 2212749886629912518944327 := by
  unfold tailWord_4309315
  simp only [CollatzResearch.WordTrace]
  refine ⟨157173630383095202253353399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104782420255396801502235599 157173630383095202253353399)
  ·
    refine ⟨235760445574642803380030099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157173630383095202253353399 235760445574642803380030099)
    ·
      refine ⟨353640668361964205070045149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235760445574642803380030099 353640668361964205070045149)
      ·
        refine ⟨132615250635736576901266931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353640668361964205070045149 132615250635736576901266931)
        ·
          refine ⟨198922875953604865351900397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132615250635736576901266931 198922875953604865351900397)
          ·
            refine ⟨74596078482601824506962649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198922875953604865351900397 74596078482601824506962649)
            ·
              refine ⟨55947058861951368380221987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74596078482601824506962649 55947058861951368380221987)
              ·
                refine ⟨83920588292927052570332981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55947058861951368380221987 83920588292927052570332981)
                ·
                  refine ⟨7867555152461911178468717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83920588292927052570332981 7867555152461911178468717)
                  ·
                    refine ⟨2950333182173216691925769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7867555152461911178468717 2950333182173216691925769)
                    ·
                      refine ⟨2212749886629912518944327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950333182173216691925769 2212749886629912518944327)
                      ·
                        rfl

theorem cell23_4309315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_4309315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309315 prefixEnd_4309315 := by exact prefixLift 4309315
  have htrace : WordTrace (prefixWord ++ tailWord_4309315) baseStart_4309315 baseEnd_4309315 := by
    simpa [prefixWord, tailWord_4309315, baseEnd_4309315] using wordTrace_append hprefix tailTrace_4309315
  have hstable : (prefixWord ++ tailWord_4309315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309315).length < 2 ^ (prefixWord ++ tailWord_4309315).sum := by decide
  have hdescent : baseEnd_4309315 < baseStart_4309315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309316 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_4309316 : Nat := 118140960795 + 4309316 * 2 ^ 59
def prefixEnd_4309316 : Nat := 4983230072969 + 3 ^ 40 * 4309316 * 2
def baseEnd_4309316 : Nat := 737583466703522338343941

theorem tailTrace_4309316 : CollatzResearch.WordTrace tailWord_4309316 prefixEnd_4309316 737583466703522338343941 := by
  unfold tailWord_4309316
  simp only [CollatzResearch.WordTrace]
  refine ⟨78586833428045789712069901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104782444570727719616093201 78586833428045789712069901)
  ·
    refine ⟨29470062535517171142026213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78586833428045789712069901 29470062535517171142026213)
    ·
      refine ⟨5525636725409469589129915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29470062535517171142026213 5525636725409469589129915)
      ·
        refine ⟨8288455088114204383694873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5525636725409469589129915 8288455088114204383694873)
        ·
          refine ⟨6216341316085653287771155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8288455088114204383694873 6216341316085653287771155)
          ·
            refine ⟨9324511974128479931656733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216341316085653287771155 9324511974128479931656733)
            ·
              refine ⟨3496691990298179974371275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9324511974128479931656733 3496691990298179974371275)
              ·
                refine ⟨5245037985447269961556913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496691990298179974371275 5245037985447269961556913)
                ·
                  refine ⟨3933778489085452471167685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5245037985447269961556913 3933778489085452471167685)
                  ·
                    refine ⟨737583466703522338343941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933778489085452471167685 737583466703522338343941)
                    ·
                      rfl

theorem cell23_4309316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_4309316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309316 prefixEnd_4309316 := by exact prefixLift 4309316
  have htrace : WordTrace (prefixWord ++ tailWord_4309316) baseStart_4309316 baseEnd_4309316 := by
    simpa [prefixWord, tailWord_4309316, baseEnd_4309316] using wordTrace_append hprefix tailTrace_4309316
  have hstable : (prefixWord ++ tailWord_4309316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309316).length < 2 ^ (prefixWord ++ tailWord_4309316).sum := by decide
  have hdescent : baseEnd_4309316 < baseStart_4309316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309340 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4309340 : Nat := 118140960795 + 4309340 * 2 ^ 59
def prefixEnd_4309340 : Nat := 4983230072969 + 3 ^ 40 * 4309340 * 2
def baseEnd_4309340 : Nat := 2212762723646274921131713

theorem tailTrace_4309340 : CollatzResearch.WordTrace tailWord_4309340 prefixEnd_4309340 2212762723646274921131713 := by
  unfold tailWord_4309340
  simp only [CollatzResearch.WordTrace]
  refine ⟨78587271104002315761506737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104783028138669754348675649 78587271104002315761506737)
  ·
    refine ⟨58940453328001736821130053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78587271104002315761506737 58940453328001736821130053)
    ·
      refine ⟨11051334999000325653961885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58940453328001736821130053 11051334999000325653961885)
      ·
        refine ⟨4144250624625122120235707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11051334999000325653961885 4144250624625122120235707)
        ·
          refine ⟨6216375936937683180353561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144250624625122120235707 6216375936937683180353561)
          ·
            refine ⟨4662281952703262385265171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6216375936937683180353561 4662281952703262385265171)
            ·
              refine ⟨6993422929054893577897757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662281952703262385265171 6993422929054893577897757)
              ·
                refine ⟨2622533598395585091711659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6993422929054893577897757 2622533598395585091711659)
                ·
                  refine ⟨3933800397593377637567489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622533598395585091711659 3933800397593377637567489)
                  ·
                    refine ⟨2950350298195033228175617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3933800397593377637567489 2950350298195033228175617)
                    ·
                      refine ⟨2212762723646274921131713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950350298195033228175617 2212762723646274921131713)
                      ·
                        rfl

theorem cell23_4309340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4309340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309340 prefixEnd_4309340 := by exact prefixLift 4309340
  have htrace : WordTrace (prefixWord ++ tailWord_4309340) baseStart_4309340 baseEnd_4309340 := by
    simpa [prefixWord, tailWord_4309340, baseEnd_4309340] using wordTrace_append hprefix tailTrace_4309340
  have hstable : (prefixWord ++ tailWord_4309340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309340).length < 2 ^ (prefixWord ++ tailWord_4309340).sum := by decide
  have hdescent : baseEnd_4309340 < baseStart_4309340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309425 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4309425 : Nat := 118140960795 + 4309425 * 2 ^ 59
def prefixEnd_4309425 : Nat := 4983230072969 + 3 ^ 40 * 4309425 * 2
def baseEnd_4309425 : Nat := 2212806369501907088568821

theorem tailTrace_4309425 : CollatzResearch.WordTrace tailWord_4309425 prefixEnd_4309425 2212806369501907088568821 := by
  unfold tailWord_4309425
  simp only [CollatzResearch.WordTrace]
  refine ⟨157177642412696691039857729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104785094941797794026571819 157177642412696691039857729)
  ·
    refine ⟨117883231809522518279893297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157177642412696691039857729 117883231809522518279893297)
    ·
      refine ⟨88412423857141888709919973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117883231809522518279893297 88412423857141888709919973)
      ·
        refine ⟨16577329473214104133109995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88412423857141888709919973 16577329473214104133109995)
        ·
          refine ⟨24865994209821156199664993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16577329473214104133109995 24865994209821156199664993)
          ·
            refine ⟨18649495657365867149748745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24865994209821156199664993 18649495657365867149748745)
            ·
              refine ⟨13987121743024400362311559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18649495657365867149748745 13987121743024400362311559)
              ·
                refine ⟨20980682614536600543467339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13987121743024400362311559 20980682614536600543467339)
                ·
                  refine ⟨31471023921804900815201009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20980682614536600543467339 31471023921804900815201009)
                  ·
                    refine ⟨23603267941353675611400757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31471023921804900815201009 23603267941353675611400757)
                    ·
                      refine ⟨2212806369501907088568821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23603267941353675611400757 2212806369501907088568821)
                      ·
                        rfl

theorem cell23_4309425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4309425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309425 prefixEnd_4309425 := by exact prefixLift 4309425
  have htrace : WordTrace (prefixWord ++ tailWord_4309425) baseStart_4309425 baseEnd_4309425 := by
    simpa [prefixWord, tailWord_4309425, baseEnd_4309425] using wordTrace_append hprefix tailTrace_4309425
  have hstable : (prefixWord ++ tailWord_4309425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309425).length < 2 ^ (prefixWord ++ tailWord_4309425).sum := by decide
  have hdescent : baseEnd_4309425 < baseStart_4309425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309452 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4309452 : Nat := 118140960795 + 4309452 * 2 ^ 59
def prefixEnd_4309452 : Nat := 4983230072969 + 3 ^ 40 * 4309452 * 2
def baseEnd_4309452 : Nat := 2212820233479578482931197

theorem tailTrace_4309452 : CollatzResearch.WordTrace tailWord_4309452 prefixEnd_4309452 2212820233479578482931197 := by
  unfold tailWord_4309452
  simp only [CollatzResearch.WordTrace]
  refine ⟨78589313591799437325545305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104785751455732583100727073 78589313591799437325545305)
  ·
    refine ⟨58941985193849577994158979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78589313591799437325545305 58941985193849577994158979)
    ·
      refine ⟨88412977790774366991238469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58941985193849577994158979 88412977790774366991238469)
      ·
        refine ⟨16577433335770193810857213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88412977790774366991238469 16577433335770193810857213)
        ·
          refine ⟨6216537500913822679071455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16577433335770193810857213 6216537500913822679071455)
          ·
            refine ⟨9324806251370734018607183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216537500913822679071455 9324806251370734018607183)
            ·
              refine ⟨13987209377056101027910775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9324806251370734018607183 13987209377056101027910775)
              ·
                refine ⟨20980814065584151541866163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13987209377056101027910775 20980814065584151541866163)
                ·
                  refine ⟨31471221098376227312799245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20980814065584151541866163 31471221098376227312799245)
                  ·
                    refine ⟨11801707911891085242299717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31471221098376227312799245 11801707911891085242299717)
                    ·
                      refine ⟨2212820233479578482931197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11801707911891085242299717 2212820233479578482931197)
                      ·
                        rfl

theorem cell23_4309452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4309452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309452 prefixEnd_4309452 := by exact prefixLift 4309452
  have htrace : WordTrace (prefixWord ++ tailWord_4309452) baseStart_4309452 baseEnd_4309452 := by
    simpa [prefixWord, tailWord_4309452, baseEnd_4309452] using wordTrace_append hprefix tailTrace_4309452
  have hstable : (prefixWord ++ tailWord_4309452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309452).length < 2 ^ (prefixWord ++ tailWord_4309452).sum := by decide
  have hdescent : baseEnd_4309452 < baseStart_4309452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309479 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 1, 4]
def baseStart_4309479 : Nat := 118140960795 + 4309479 * 2 ^ 59
def prefixEnd_4309479 : Nat := 4983230072969 + 3 ^ 40 * 4309479 * 2
def baseEnd_4309479 : Nat := 737611365819083292431191

theorem tailTrace_4309479 : CollatzResearch.WordTrace tailWord_4309479 prefixEnd_4309479 737611365819083292431191 := by
  unfold tailWord_4309479
  simp only [CollatzResearch.WordTrace]
  refine ⟨157179611954501058262323491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104786407969667372174882327 157179611954501058262323491)
  ·
    refine ⟨235769417931751587393485237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157179611954501058262323491 235769417931751587393485237)
    ·
      refine ⟨22103382931101711318139241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235769417931751587393485237 22103382931101711318139241)
      ·
        refine ⟨16577537198326283488604431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22103382931101711318139241 16577537198326283488604431)
        ·
          refine ⟨24866305797489425232906647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16577537198326283488604431 24866305797489425232906647)
          ·
            refine ⟨37299458696234137849359971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24866305797489425232906647 37299458696234137849359971)
            ·
              refine ⟨55949188044351206774039957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37299458696234137849359971 55949188044351206774039957)
              ·
                refine ⟨2622618189578962817533123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55949188044351206774039957 2622618189578962817533123)
                ·
                  refine ⟨3933927284368444226299685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622618189578962817533123 3933927284368444226299685)
                  ·
                    refine ⟨737611365819083292431191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3933927284368444226299685 737611365819083292431191)
                    ·
                      rfl

theorem cell23_4309479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_4309479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309479 prefixEnd_4309479 := by exact prefixLift 4309479
  have htrace : WordTrace (prefixWord ++ tailWord_4309479) baseStart_4309479 baseEnd_4309479 := by
    simpa [prefixWord, tailWord_4309479, baseEnd_4309479] using wordTrace_append hprefix tailTrace_4309479
  have hstable : (prefixWord ++ tailWord_4309479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309479).length < 2 ^ (prefixWord ++ tailWord_4309479).sum := by decide
  have hdescent : baseEnd_4309479 < baseStart_4309479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309543 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 6]
def baseStart_4309543 : Nat := 118140960795 + 4309543 * 2 ^ 59
def prefixEnd_4309543 : Nat := 4983230072969 + 3 ^ 40 * 4309543 * 2
def baseEnd_4309543 : Nat := 245874106691015291877031

theorem tailTrace_4309543 : CollatzResearch.WordTrace tailWord_4309543 prefixEnd_4309543 245874106691015291877031 := by
  unfold tailWord_4309543
  simp only [CollatzResearch.WordTrace]
  refine ⟨157181946226269197192653283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104787964150846131461768855 157181946226269197192653283)
  ·
    refine ⟨235772919339403795788979925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157181946226269197192653283 235772919339403795788979925)
    ·
      refine ⟨5525927797017276463804217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 235772919339403795788979925 5525927797017276463804217)
      ·
        refine ⟨4144445847762957347853163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5525927797017276463804217 4144445847762957347853163)
        ·
          refine ⟨6216668771644436021779745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144445847762957347853163 6216668771644436021779745)
          ·
            refine ⟨4662501578733327016334809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6216668771644436021779745 4662501578733327016334809)
            ·
              refine ⟨3496876184049995262251107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4662501578733327016334809 3496876184049995262251107)
              ·
                refine ⟨5245314276074992893376661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496876184049995262251107 5245314276074992893376661)
                ·
                  refine ⟨245874106691015291877031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5245314276074992893376661 245874106691015291877031)
                  ·
                    rfl

theorem cell23_4309543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 6].length) (baseStart_4309543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309543 prefixEnd_4309543 := by exact prefixLift 4309543
  have htrace : WordTrace (prefixWord ++ tailWord_4309543) baseStart_4309543 baseEnd_4309543 := by
    simpa [prefixWord, tailWord_4309543, baseEnd_4309543] using wordTrace_append hprefix tailTrace_4309543
  have hstable : (prefixWord ++ tailWord_4309543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309543).length < 2 ^ (prefixWord ++ tailWord_4309543).sum := by decide
  have hdescent : baseEnd_4309543 < baseStart_4309543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309555 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_4309555 : Nat := 118140960795 + 4309555 * 2 ^ 59
def prefixEnd_4309555 : Nat := 4983230072969 + 3 ^ 40 * 4309555 * 2
def baseEnd_4309555 : Nat := 2212873121986991579943223

theorem tailTrace_4309555 : CollatzResearch.WordTrace tailWord_4309555 prefixEnd_4309555 2212873121986991579943223 := by
  unfold tailWord_4309555
  simp only [CollatzResearch.WordTrace]
  refine ⟨157182383902225723242090119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104788255934817148828060079 157182383902225723242090119)
  ·
    refine ⟨235773575853338584863135179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157182383902225723242090119 235773575853338584863135179)
    ·
      refine ⟨353660363780007877294702769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235773575853338584863135179 353660363780007877294702769)
      ·
        refine ⟨265245272835005907971027077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353660363780007877294702769 265245272835005907971027077)
        ·
          refine ⟨49733488656563607744567577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265245272835005907971027077 49733488656563607744567577)
          ·
            refine ⟨37300116492422705808425683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49733488656563607744567577 37300116492422705808425683)
            ·
              refine ⟨55950174738634058712638525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37300116492422705808425683 55950174738634058712638525)
              ·
                refine ⟨20981315526987772017239447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55950174738634058712638525 20981315526987772017239447)
                ·
                  refine ⟨31471973290481658025859171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20981315526987772017239447 31471973290481658025859171)
                  ·
                    refine ⟨47207959935722487038788757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31471973290481658025859171 47207959935722487038788757)
                    ·
                      refine ⟨2212873121986991579943223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47207959935722487038788757 2212873121986991579943223)
                      ·
                        rfl

theorem cell23_4309555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_4309555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309555 prefixEnd_4309555 := by exact prefixLift 4309555
  have htrace : WordTrace (prefixWord ++ tailWord_4309555) baseStart_4309555 baseEnd_4309555 := by
    simpa [prefixWord, tailWord_4309555, baseEnd_4309555] using wordTrace_append hprefix tailTrace_4309555
  have hstable : (prefixWord ++ tailWord_4309555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309555).length < 2 ^ (prefixWord ++ tailWord_4309555).sum := by decide
  have hdescent : baseEnd_4309555 < baseStart_4309555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309556 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4309556 : Nat := 118140960795 + 4309556 * 2 ^ 59
def prefixEnd_4309556 : Nat := 4983230072969 + 3 ^ 40 * 4309556 * 2
def baseEnd_4309556 : Nat := 737624545155882025343573

theorem tailTrace_4309556 : CollatzResearch.WordTrace tailWord_4309556 prefixEnd_4309556 737624545155882025343573 := by
  unfold tailWord_4309556
  simp only [CollatzResearch.WordTrace]
  refine ⟨78591210187611050206438261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104788280250148066941917681 78591210187611050206438261)
  ·
    refine ⟨7367925955088535956853587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78591210187611050206438261 7367925955088535956853587)
    ·
      refine ⟨11051888932632803935280381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7367925955088535956853587 11051888932632803935280381)
      ·
        refine ⟨4144458349737301475730143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11051888932632803935280381 4144458349737301475730143)
        ·
          refine ⟨6216687524605952213595215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144458349737301475730143 6216687524605952213595215)
          ·
            refine ⟨9325031286908928320392823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216687524605952213595215 9325031286908928320392823)
            ·
              refine ⟨13987546930363392480589235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9325031286908928320392823 13987546930363392480589235)
              ·
                refine ⟨20981320395545088720883853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13987546930363392480589235 20981320395545088720883853)
                ·
                  refine ⟨7867995148329408270331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20981320395545088720883853 7867995148329408270331445)
                  ·
                    refine ⟨737624545155882025343573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7867995148329408270331445 737624545155882025343573)
                    ·
                      rfl

theorem cell23_4309556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4309556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309556 prefixEnd_4309556 := by exact prefixLift 4309556
  have htrace : WordTrace (prefixWord ++ tailWord_4309556) baseStart_4309556 baseEnd_4309556 := by
    simpa [prefixWord, tailWord_4309556, baseEnd_4309556] using wordTrace_append hprefix tailTrace_4309556
  have hstable : (prefixWord ++ tailWord_4309556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309556).length < 2 ^ (prefixWord ++ tailWord_4309556).sum := by decide
  have hdescent : baseEnd_4309556 < baseStart_4309556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309559 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_4309559 : Nat := 118140960795 + 4309559 * 2 ^ 59
def prefixEnd_4309559 : Nat := 4983230072969 + 3 ^ 40 * 4309559 * 2
def baseEnd_4309559 : Nat := 2212875175909609564293205

theorem tailTrace_4309559 : CollatzResearch.WordTrace tailWord_4309559 prefixEnd_4309559 2212875175909609564293205 := by
  unfold tailWord_4309559
  simp only [CollatzResearch.WordTrace]
  refine ⟨157182529794211231925235731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104788353196140821283490487 157182529794211231925235731)
  ·
    refine ⟨235773794691316847887853597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157182529794211231925235731 235773794691316847887853597)
    ·
      refine ⟨88415173009243817957945099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235773794691316847887853597 88415173009243817957945099)
      ·
        refine ⟨132622759513865726936917649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88415173009243817957945099 132622759513865726936917649)
        ·
          refine ⟨99467069635399295202688237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132622759513865726936917649 99467069635399295202688237)
          ·
            refine ⟨37300151113274735701008089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99467069635399295202688237 37300151113274735701008089)
            ·
              refine ⟨27975113334956051775756067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37300151113274735701008089 27975113334956051775756067)
              ·
                refine ⟨41962670002434077663634101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27975113334956051775756067 41962670002434077663634101)
                ·
                  refine ⟨3934000312728194780965697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41962670002434077663634101 3934000312728194780965697)
                  ·
                    refine ⟨2950500234546146085724273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934000312728194780965697 2950500234546146085724273)
                    ·
                      refine ⟨2212875175909609564293205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950500234546146085724273 2212875175909609564293205)
                      ·
                        rfl

theorem cell23_4309559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_4309559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309559 prefixEnd_4309559 := by exact prefixLift 4309559
  have htrace : WordTrace (prefixWord ++ tailWord_4309559) baseStart_4309559 baseEnd_4309559 := by
    simpa [prefixWord, tailWord_4309559, baseEnd_4309559] using wordTrace_append hprefix tailTrace_4309559
  have hstable : (prefixWord ++ tailWord_4309559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309559).length < 2 ^ (prefixWord ++ tailWord_4309559).sum := by decide
  have hdescent : baseEnd_4309559 < baseStart_4309559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309736 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_4309736 : Nat := 118140960795 + 4309736 * 2 ^ 59
def prefixEnd_4309736 : Nat := 4983230072969 + 3 ^ 40 * 4309736 * 2
def baseEnd_4309736 : Nat := 737655353995151790593297

theorem tailTrace_4309736 : CollatzResearch.WordTrace tailWord_4309736 prefixEnd_4309736 737655353995151790593297 := by
  unfold tailWord_4309736
  simp only [CollatzResearch.WordTrace]
  refine ⟨78594492757284995577214531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104792657009713327436286041 78594492757284995577214531)
  ·
    refine ⟨117891739135927493365821797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78594492757284995577214531 117891739135927493365821797)
    ·
      refine ⟨22104701087986405006091587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117891739135927493365821797 22104701087986405006091587)
      ·
        refine ⟨33157051631979607509137381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22104701087986405006091587 33157051631979607509137381)
        ·
          refine ⟨6216947180996176407963259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33157051631979607509137381 6216947180996176407963259)
          ·
            refine ⟨9325420771494264611944889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6216947180996176407963259 9325420771494264611944889)
            ·
              refine ⟨6994065578620698458958667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9325420771494264611944889 6994065578620698458958667)
              ·
                refine ⟨10491098367931047688438001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994065578620698458958667 10491098367931047688438001)
                ·
                  refine ⟨7868323775948285766328501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10491098367931047688438001 7868323775948285766328501)
                  ·
                    refine ⟨737655353995151790593297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7868323775948285766328501 737655353995151790593297)
                    ·
                      rfl

theorem cell23_4309736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_4309736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309736 prefixEnd_4309736 := by exact prefixLift 4309736
  have htrace : WordTrace (prefixWord ++ tailWord_4309736) baseStart_4309736 baseEnd_4309736 := by
    simpa [prefixWord, tailWord_4309736, baseEnd_4309736] using wordTrace_append hprefix tailTrace_4309736
  have hstable : (prefixWord ++ tailWord_4309736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309736).length < 2 ^ (prefixWord ++ tailWord_4309736).sum := by decide
  have hdescent : baseEnd_4309736 < baseStart_4309736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309739 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 4, 4, 2]
def baseStart_4309739 : Nat := 118140960795 + 4309739 * 2 ^ 59
def prefixEnd_4309739 : Nat := 4983230072969 + 3 ^ 40 * 4309739 * 2
def baseEnd_4309739 : Nat := 2212967602427418860042377

theorem tailTrace_4309739 : CollatzResearch.WordTrace tailWord_4309739 prefixEnd_4309739 2212967602427418860042377 := by
  unfold tailWord_4309739
  simp only [CollatzResearch.WordTrace]
  refine ⟨157189094933559122666788271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104792729955706081777858847 157189094933559122666788271)
  ·
    refine ⟨235783642400338684000182407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157189094933559122666788271 235783642400338684000182407)
    ·
      refine ⟨353675463600508026000273611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235783642400338684000182407 353675463600508026000273611)
      ·
        refine ⟨530513195400762039000410417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353675463600508026000273611 530513195400762039000410417)
        ·
          refine ⟨397884896550571529250307813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530513195400762039000410417 397884896550571529250307813)
          ·
            refine ⟨74603418103232161734432715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 397884896550571529250307813 74603418103232161734432715)
            ·
              refine ⟨111905127154848242601649073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74603418103232161734432715 111905127154848242601649073)
              ·
                refine ⟨83928845366136181951236805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111905127154848242601649073 83928845366136181951236805)
                ·
                  refine ⟨15736658506150534115856901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83928845366136181951236805 15736658506150534115856901)
                  ·
                    refine ⟨2950623469903225146723169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15736658506150534115856901 2950623469903225146723169)
                    ·
                      refine ⟨2212967602427418860042377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950623469903225146723169 2212967602427418860042377)
                      ·
                        rfl

theorem cell23_4309739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4, 2].length) (baseStart_4309739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309739 prefixEnd_4309739 := by exact prefixLift 4309739
  have htrace : WordTrace (prefixWord ++ tailWord_4309739) baseStart_4309739 baseEnd_4309739 := by
    simpa [prefixWord, tailWord_4309739, baseEnd_4309739] using wordTrace_append hprefix tailTrace_4309739
  have hstable : (prefixWord ++ tailWord_4309739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309739).length < 2 ^ (prefixWord ++ tailWord_4309739).sum := by decide
  have hdescent : baseEnd_4309739 < baseStart_4309739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309752 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_4309752 : Nat := 118140960795 + 4309752 * 2 ^ 59
def prefixEnd_4309752 : Nat := 4983230072969 + 3 ^ 40 * 4309752 * 2
def baseEnd_4309752 : Nat := 2212974277675927309179817

theorem tailTrace_4309752 : CollatzResearch.WordTrace tailWord_4309752 prefixEnd_4309752 2212974277675927309179817 := by
  unfold tailWord_4309752
  simp only [CollatzResearch.WordTrace]
  refine ⟨78594784541256012943505755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104793046055008017258007673 78594784541256012943505755)
  ·
    refine ⟨117892176811884019415258633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78594784541256012943505755 117892176811884019415258633)
    ·
      refine ⟨88419132608913014561443975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117892176811884019415258633 88419132608913014561443975)
      ·
        refine ⟨132628698913369521842165963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88419132608913014561443975 132628698913369521842165963)
        ·
          refine ⟨198943048370054282763248945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132628698913369521842165963 198943048370054282763248945)
          ·
            refine ⟨149207286277540712072436709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198943048370054282763248945 149207286277540712072436709)
            ·
              refine ⟨27976366177038883513581883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149207286277540712072436709 27976366177038883513581883)
              ·
                refine ⟨41964549265558325270372825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27976366177038883513581883 41964549265558325270372825)
                ·
                  refine ⟨31473411949168743952779619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41964549265558325270372825 31473411949168743952779619)
                  ·
                    refine ⟨47210117923753115929169429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31473411949168743952779619 47210117923753115929169429)
                    ·
                      refine ⟨2212974277675927309179817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47210117923753115929169429 2212974277675927309179817)
                      ·
                        rfl

theorem cell23_4309752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_4309752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309752 prefixEnd_4309752 := by exact prefixLift 4309752
  have htrace : WordTrace (prefixWord ++ tailWord_4309752) baseStart_4309752 baseEnd_4309752 := by
    simpa [prefixWord, tailWord_4309752, baseEnd_4309752] using wordTrace_append hprefix tailTrace_4309752
  have hstable : (prefixWord ++ tailWord_4309752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309752).length < 2 ^ (prefixWord ++ tailWord_4309752).sum := by decide
  have hdescent : baseEnd_4309752 < baseStart_4309752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309816 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_4309816 : Nat := 118140960795 + 4309816 * 2 ^ 59
def prefixEnd_4309816 : Nat := 4983230072969 + 3 ^ 40 * 4309816 * 2
def baseEnd_4309816 : Nat := 2213007140437815058779523

theorem tailTrace_4309816 : CollatzResearch.WordTrace tailWord_4309816 prefixEnd_4309816 2213007140437815058779523 := by
  unfold tailWord_4309816
  simp only [CollatzResearch.WordTrace]
  refine ⟨78595951677140082408670651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104794602236186776544894201 78595951677140082408670651)
  ·
    refine ⟨117893927515710123613005977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78595951677140082408670651 117893927515710123613005977)
    ·
      refine ⟨88420445636782592709754483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117893927515710123613005977 88420445636782592709754483)
      ·
        refine ⟨132630668455173889064631725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88420445636782592709754483 132630668455173889064631725)
        ·
          refine ⟨49736500670690208399236897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132630668455173889064631725 49736500670690208399236897)
          ·
            refine ⟨37302375503017656299427673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49736500670690208399236897 37302375503017656299427673)
            ·
              refine ⟨27976781627263242224570755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37302375503017656299427673 27976781627263242224570755)
              ·
                refine ⟨41965172440894863336856133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27976781627263242224570755 41965172440894863336856133)
                ·
                  refine ⟨7868469832667786875660525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41965172440894863336856133 7868469832667786875660525)
                  ·
                    refine ⟨2950676187250420078372697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7868469832667786875660525 2950676187250420078372697)
                    ·
                      refine ⟨2213007140437815058779523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950676187250420078372697 2213007140437815058779523)
                      ·
                        rfl

theorem cell23_4309816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_4309816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309816 prefixEnd_4309816 := by exact prefixLift 4309816
  have htrace : WordTrace (prefixWord ++ tailWord_4309816) baseStart_4309816 baseEnd_4309816 := by
    simpa [prefixWord, tailWord_4309816, baseEnd_4309816] using wordTrace_append hprefix tailTrace_4309816
  have hstable : (prefixWord ++ tailWord_4309816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309816).length < 2 ^ (prefixWord ++ tailWord_4309816).sum := by decide
  have hdescent : baseEnd_4309816 < baseStart_4309816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309823 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 3]
def baseStart_4309823 : Nat := 118140960795 + 4309823 * 2 ^ 59
def prefixEnd_4309823 : Nat := 4983230072969 + 3 ^ 40 * 4309823 * 2
def baseEnd_4309823 : Nat := 2213010734802396531391991

theorem tailTrace_4309823 : CollatzResearch.WordTrace tailWord_4309823 prefixEnd_4309823 2213010734802396531391991 := by
  unfold tailWord_4309823
  simp only [CollatzResearch.WordTrace]
  refine ⟨157192158665254805012846123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104794772443503203341897415 157192158665254805012846123)
  ·
    refine ⟨235788237997882207519269185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157192158665254805012846123 235788237997882207519269185)
    ·
      refine ⟨176841178498411655639451889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235788237997882207519269185 176841178498411655639451889)
      ·
        refine ⟨132630883873808741729588917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176841178498411655639451889 132630883873808741729588917)
        ·
          refine ⟨12434145363169569537148961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132630883873808741729588917 12434145363169569537148961)
          ·
            refine ⟨9325609022377177152861721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12434145363169569537148961 9325609022377177152861721)
            ·
              refine ⟨6994206766782882864646291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9325609022377177152861721 6994206766782882864646291)
              ·
                refine ⟨10491310150174324296969437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994206766782882864646291 10491310150174324296969437)
                ·
                  refine ⟨3934241306315371611363539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10491310150174324296969437 3934241306315371611363539)
                  ·
                    refine ⟨5901361959473057417045309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3934241306315371611363539 5901361959473057417045309)
                    ·
                      refine ⟨2213010734802396531391991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5901361959473057417045309 2213010734802396531391991)
                      ·
                        rfl

theorem cell23_4309823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_4309823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309823 prefixEnd_4309823 := by exact prefixLift 4309823
  have htrace : WordTrace (prefixWord ++ tailWord_4309823) baseStart_4309823 baseEnd_4309823 := by
    simpa [prefixWord, tailWord_4309823, baseEnd_4309823] using wordTrace_append hprefix tailTrace_4309823
  have hstable : (prefixWord ++ tailWord_4309823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309823).length < 2 ^ (prefixWord ++ tailWord_4309823).sum := by decide
  have hdescent : baseEnd_4309823 < baseStart_4309823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309829 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_4309829 : Nat := 118140960795 + 4309829 * 2 ^ 59
def prefixEnd_4309829 : Nat := 4983230072969 + 3 ^ 40 * 4309829 * 2
def baseEnd_4309829 : Nat := 2213013815686323507916963

theorem tailTrace_4309829 : CollatzResearch.WordTrace tailWord_4309829 prefixEnd_4309829 2213013815686323507916963 := by
  unfold tailWord_4309829
  simp only [CollatzResearch.WordTrace]
  refine ⟨157192377503233068037564541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104794918335488712025043027 157192377503233068037564541)
  ·
    refine ⟨58947141563712400514086703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157192377503233068037564541 58947141563712400514086703)
    ·
      refine ⟨88420712345568600771130055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58947141563712400514086703 88420712345568600771130055)
      ·
        refine ⟨132631068518352901156695083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88420712345568600771130055 132631068518352901156695083)
        ·
          refine ⟨198946602777529351735042625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132631068518352901156695083 198946602777529351735042625)
          ·
            refine ⟨149209952083147013801281969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198946602777529351735042625 149209952083147013801281969)
            ·
              refine ⟨111907464062360260350961477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149209952083147013801281969 111907464062360260350961477)
              ·
                refine ⟨20982649511692548815805277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111907464062360260350961477 20982649511692548815805277)
                ·
                  refine ⟨7868493566884705805926979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20982649511692548815805277 7868493566884705805926979)
                  ·
                    refine ⟨11802740350327058708890469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7868493566884705805926979 11802740350327058708890469)
                    ·
                      refine ⟨2213013815686323507916963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11802740350327058708890469 2213013815686323507916963)
                      ·
                        rfl

theorem cell23_4309829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_4309829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309829 prefixEnd_4309829 := by exact prefixLift 4309829
  have htrace : WordTrace (prefixWord ++ tailWord_4309829) baseStart_4309829 baseEnd_4309829 := by
    simpa [prefixWord, tailWord_4309829, baseEnd_4309829] using wordTrace_append hprefix tailTrace_4309829
  have hstable : (prefixWord ++ tailWord_4309829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309829).length < 2 ^ (prefixWord ++ tailWord_4309829).sum := by decide
  have hdescent : baseEnd_4309829 < baseStart_4309829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309910 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4309910 : Nat := 118140960795 + 4309910 * 2 ^ 59
def prefixEnd_4309910 : Nat := 4983230072969 + 3 ^ 40 * 4309910 * 2
def baseEnd_4309910 : Nat := 2213055407619337691004091

theorem tailTrace_4309910 : CollatzResearch.WordTrace tailWord_4309910 prefixEnd_4309910 2213055407619337691004091 := by
  unfold tailWord_4309910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824708238496226179453949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104796887877293079247508789 9824708238496226179453949)
  ·
    refine ⟨3684265589436084817295231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9824708238496226179453949 3684265589436084817295231)
    ·
      refine ⟨5526398384154127225942847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3684265589436084817295231 5526398384154127225942847)
      ·
        refine ⟨8289597576231190838914271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5526398384154127225942847 8289597576231190838914271)
        ·
          refine ⟨12434396364346786258371407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289597576231190838914271 12434396364346786258371407)
          ·
            refine ⟨18651594546520179387557111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434396364346786258371407 18651594546520179387557111)
            ·
              refine ⟨27977391819780269081335667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18651594546520179387557111 27977391819780269081335667)
              ·
                refine ⟨41966087729670403622003501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27977391819780269081335667 41966087729670403622003501)
                ·
                  refine ⟨15737282898626401358251313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41966087729670403622003501 15737282898626401358251313)
                  ·
                    refine ⟨11802962173969801018688485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15737282898626401358251313 11802962173969801018688485)
                    ·
                      refine ⟨2213055407619337691004091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11802962173969801018688485 2213055407619337691004091)
                      ·
                        rfl

theorem cell23_4309910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4309910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309910 prefixEnd_4309910 := by exact prefixLift 4309910
  have htrace : WordTrace (prefixWord ++ tailWord_4309910) baseStart_4309910 baseEnd_4309910 := by
    simpa [prefixWord, tailWord_4309910, baseEnd_4309910] using wordTrace_append hprefix tailTrace_4309910
  have hstable : (prefixWord ++ tailWord_4309910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309910).length < 2 ^ (prefixWord ++ tailWord_4309910).sum := by decide
  have hdescent : baseEnd_4309910 < baseStart_4309910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309923 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 1, 3, 2]
def baseStart_4309923 : Nat := 118140960795 + 4309923 * 2 ^ 59
def prefixEnd_4309923 : Nat := 4983230072969 + 3 ^ 40 * 4309923 * 2
def baseEnd_4309923 : Nat := 2213062082867846140141531

theorem tailTrace_4309923 : CollatzResearch.WordTrace tailWord_4309923 prefixEnd_4309923 2213062082867846140141531 := by
  unfold tailWord_4309923
  simp only [CollatzResearch.WordTrace]
  refine ⟨157195805964892522091486423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104797203976595014727657615 157195805964892522091486423)
  ·
    refine ⟨235793708947338783137229635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157195805964892522091486423 235793708947338783137229635)
    ·
      refine ⟨353690563421008174705844453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235793708947338783137229635 353690563421008174705844453)
      ·
        refine ⟨66316980641439032757345835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 353690563421008174705844453 66316980641439032757345835)
        ·
          refine ⟨99475470962158549136018753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66316980641439032757345835 99475470962158549136018753)
          ·
            refine ⟨74606603221618911852014065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99475470962158549136018753 74606603221618911852014065)
            ·
              refine ⟨55954952416214183889010549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74606603221618911852014065 55954952416214183889010549)
              ·
                refine ⟨5245776789020079739594739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55954952416214183889010549 5245776789020079739594739)
                ·
                  refine ⟨7868665183530119609392109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245776789020079739594739 7868665183530119609392109)
                  ·
                    refine ⟨2950749443823794853522041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7868665183530119609392109 2950749443823794853522041)
                    ·
                      refine ⟨2213062082867846140141531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950749443823794853522041 2213062082867846140141531)
                      ·
                        rfl

theorem cell23_4309923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_4309923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309923 prefixEnd_4309923 := by exact prefixLift 4309923
  have htrace : WordTrace (prefixWord ++ tailWord_4309923) baseStart_4309923 baseEnd_4309923 := by
    simpa [prefixWord, tailWord_4309923, baseEnd_4309923] using wordTrace_append hprefix tailTrace_4309923
  have hstable : (prefixWord ++ tailWord_4309923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309923).length < 2 ^ (prefixWord ++ tailWord_4309923).sum := by decide
  have hdescent : baseEnd_4309923 < baseStart_4309923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309929 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_4309929 : Nat := 118140960795 + 4309929 * 2 ^ 59
def prefixEnd_4309929 : Nat := 4983230072969 + 3 ^ 40 * 4309929 * 2
def baseEnd_4309929 : Nat := 737688387917257705555501

theorem tailTrace_4309929 : CollatzResearch.WordTrace tailWord_4309929 prefixEnd_4309929 737688387917257705555501 := by
  unfold tailWord_4309929
  simp only [CollatzResearch.WordTrace]
  refine ⟨157196024802870785116204841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104797349868580523410803227 157196024802870785116204841)
  ·
    refine ⟨117897018602153088837153631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157196024802870785116204841 117897018602153088837153631)
    ·
      refine ⟨176845527903229633255730447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117897018602153088837153631 176845527903229633255730447)
      ·
        refine ⟨265268291854844449883595671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176845527903229633255730447 265268291854844449883595671)
        ·
          refine ⟨397902437782266674825393507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265268291854844449883595671 397902437782266674825393507)
          ·
            refine ⟨596853656673400012238090261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397902437782266674825393507 596853656673400012238090261)
            ·
              refine ⟨27977515156565625573660481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 596853656673400012238090261 27977515156565625573660481)
              ·
                refine ⟨20983136367424219180245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27977515156565625573660481 20983136367424219180245361)
                ·
                  refine ⟨15737352275568164385184021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20983136367424219180245361 15737352275568164385184021)
                  ·
                    refine ⟨737688387917257705555501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15737352275568164385184021 737688387917257705555501)
                    ·
                      rfl

theorem cell23_4309929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_4309929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309929 prefixEnd_4309929 := by exact prefixLift 4309929
  have htrace : WordTrace (prefixWord ++ tailWord_4309929) baseStart_4309929 baseEnd_4309929 := by
    simpa [prefixWord, tailWord_4309929, baseEnd_4309929] using wordTrace_append hprefix tailTrace_4309929
  have hstable : (prefixWord ++ tailWord_4309929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309929).length < 2 ^ (prefixWord ++ tailWord_4309929).sum := by decide
  have hdescent : baseEnd_4309929 < baseStart_4309929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309939 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_4309939 : Nat := 118140960795 + 4309939 * 2 ^ 59
def prefixEnd_4309939 : Nat := 4983230072969 + 3 ^ 40 * 4309939 * 2
def baseEnd_4309939 : Nat := 2213070298558318077541457

theorem tailTrace_4309939 : CollatzResearch.WordTrace tailWord_4309939 prefixEnd_4309939 2213070298558318077541457 := by
  unfold tailWord_4309939
  simp only [CollatzResearch.WordTrace]
  refine ⟨157196389532834556824068871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104797593021889704549379247 157196389532834556824068871)
  ·
    refine ⟨235794584299251835236103307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157196389532834556824068871 235794584299251835236103307)
    ·
      refine ⟨353691876448877752854154961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235794584299251835236103307 353691876448877752854154961)
      ·
        refine ⟨265268907336658314640616221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353691876448877752854154961 265268907336658314640616221)
        ·
          refine ⟨99475840251246867990231083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265268907336658314640616221 99475840251246867990231083)
          ·
            refine ⟨149213760376870301985346625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99475840251246867990231083 149213760376870301985346625)
            ·
              refine ⟨111910320282652726489009969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149213760376870301985346625 111910320282652726489009969)
              ·
                refine ⟨83932740211989544866757477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111910320282652726489009969 83932740211989544866757477)
                ·
                  refine ⟨15737388789748039662517027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83932740211989544866757477 15737388789748039662517027)
                  ·
                    refine ⟨23606083184622059493775541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15737388789748039662517027 23606083184622059493775541)
                    ·
                      refine ⟨2213070298558318077541457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23606083184622059493775541 2213070298558318077541457)
                      ·
                        rfl

theorem cell23_4309939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_4309939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309939 prefixEnd_4309939 := by exact prefixLift 4309939
  have htrace : WordTrace (prefixWord ++ tailWord_4309939) baseStart_4309939 baseEnd_4309939 := by
    simpa [prefixWord, tailWord_4309939, baseEnd_4309939] using wordTrace_append hprefix tailTrace_4309939
  have hstable : (prefixWord ++ tailWord_4309939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309939).length < 2 ^ (prefixWord ++ tailWord_4309939).sum := by decide
  have hdescent : baseEnd_4309939 < baseStart_4309939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309959 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 9]
def baseStart_4309959 : Nat := 118140960795 + 4309959 * 2 ^ 59
def prefixEnd_4309959 : Nat := 4983230072969 + 3 ^ 40 * 4309959 * 2
def baseEnd_4309959 : Nat := 245897840907934222143485

theorem tailTrace_4309959 : CollatzResearch.WordTrace tailWord_4309959 prefixEnd_4309959 245897840907934222143485 := by
  unfold tailWord_4309959
  simp only [CollatzResearch.WordTrace]
  refine ⟨157197118992762100239796931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104798079328508066826531287 157197118992762100239796931)
  ·
    refine ⟨235795678489143150359695397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157197118992762100239796931 235795678489143150359695397)
    ·
      refine ⟨44211689716714340692442887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235795678489143150359695397 44211689716714340692442887)
      ·
        refine ⟨66317534575071511038664331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44211689716714340692442887 66317534575071511038664331)
        ·
          refine ⟨99476301862607266557996497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66317534575071511038664331 99476301862607266557996497)
          ·
            refine ⟨74607226396955449918497373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99476301862607266557996497 74607226396955449918497373)
            ·
              refine ⟨27977709898858293719436515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74607226396955449918497373 27977709898858293719436515)
              ·
                refine ⟨41966564848287440579154773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27977709898858293719436515 41966564848287440579154773)
                ·
                  refine ⟨245897840907934222143485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41966564848287440579154773 245897840907934222143485)
                  ·
                    rfl

theorem cell23_4309959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 9].length) (baseStart_4309959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309959 prefixEnd_4309959 := by exact prefixLift 4309959
  have htrace : WordTrace (prefixWord ++ tailWord_4309959) baseStart_4309959 baseEnd_4309959 := by
    simpa [prefixWord, tailWord_4309959, baseEnd_4309959] using wordTrace_append hprefix tailTrace_4309959
  have hstable : (prefixWord ++ tailWord_4309959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309959).length < 2 ^ (prefixWord ++ tailWord_4309959).sum := by decide
  have hdescent : baseEnd_4309959 < baseStart_4309959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309970 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4309970 : Nat := 118140960795 + 4309970 * 2 ^ 59
def prefixEnd_4309970 : Nat := 4983230072969 + 3 ^ 40 * 4309970 * 2
def baseEnd_4309970 : Nat := 2213086216458607456253815

theorem tailTrace_4309970 : CollatzResearch.WordTrace tailWord_4309970 prefixEnd_4309970 2213086216458607456253815 := by
  unfold tailWord_4309970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39299380048930562279611841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104798346797148166078964909 39299380048930562279611841)
  ·
    refine ⟨29474535036697921709708881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39299380048930562279611841 29474535036697921709708881)
    ·
      refine ⟨22105901277523441282281661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29474535036697921709708881 22105901277523441282281661)
      ·
        refine ⟨8289712979071290480855623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22105901277523441282281661 8289712979071290480855623)
        ·
          refine ⟨12434569468606935721283435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289712979071290480855623 12434569468606935721283435)
          ·
            refine ⟨18651854202910403581925153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434569468606935721283435 18651854202910403581925153)
            ·
              refine ⟨13988890652182802686443865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18651854202910403581925153 13988890652182802686443865)
              ·
                refine ⟨10491667989137102014832899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13988890652182802686443865 10491667989137102014832899)
                ·
                  refine ⟨15737501983705653022249349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10491667989137102014832899 15737501983705653022249349)
                  ·
                    refine ⟨2950781621944809941671753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15737501983705653022249349 2950781621944809941671753)
                    ·
                      refine ⟨2213086216458607456253815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950781621944809941671753 2213086216458607456253815)
                      ·
                        rfl

theorem cell23_4309970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4309970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309970 prefixEnd_4309970 := by exact prefixLift 4309970
  have htrace : WordTrace (prefixWord ++ tailWord_4309970) baseStart_4309970 baseEnd_4309970 := by
    simpa [prefixWord, tailWord_4309970, baseEnd_4309970] using wordTrace_append hprefix tailTrace_4309970
  have hstable : (prefixWord ++ tailWord_4309970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309970).length < 2 ^ (prefixWord ++ tailWord_4309970).sum := by decide
  have hdescent : baseEnd_4309970 < baseStart_4309970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4309974 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4309974 : Nat := 118140960795 + 4309974 * 2 ^ 59
def prefixEnd_4309974 : Nat := 4983230072969 + 3 ^ 40 * 4309974 * 2
def baseEnd_4309974 : Nat := 2213088270381225440603797

theorem tailTrace_4309974 : CollatzResearch.WordTrace tailWord_4309974 prefixEnd_4309974 2213088270381225440603797 := by
  unfold tailWord_4309974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824854130481734862599561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104798444058471838534395317 9824854130481734862599561)
  ·
    refine ⟨7368640597861301146949671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9824854130481734862599561 7368640597861301146949671)
    ·
      refine ⟨11052960896791951720424507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7368640597861301146949671 11052960896791951720424507)
      ·
        refine ⟨16579441345187927580636761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11052960896791951720424507 16579441345187927580636761)
        ·
          refine ⟨12434581008890945685477571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16579441345187927580636761 12434581008890945685477571)
          ·
            refine ⟨18651871513336418528216357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434581008890945685477571 18651871513336418528216357)
            ·
              refine ⟨3497225908750578474040567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18651871513336418528216357 3497225908750578474040567)
              ·
                refine ⟨5245838863125867711060851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497225908750578474040567 5245838863125867711060851)
                ·
                  refine ⟨7868758294688801566591277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245838863125867711060851 7868758294688801566591277)
                  ·
                    refine ⟨2950784360508300587471729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7868758294688801566591277 2950784360508300587471729)
                    ·
                      refine ⟨2213088270381225440603797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950784360508300587471729 2213088270381225440603797)
                      ·
                        rfl

theorem cell23_4309974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4309974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4309974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4309974 prefixEnd_4309974 := by exact prefixLift 4309974
  have htrace : WordTrace (prefixWord ++ tailWord_4309974) baseStart_4309974 baseEnd_4309974 := by
    simpa [prefixWord, tailWord_4309974, baseEnd_4309974] using wordTrace_append hprefix tailTrace_4309974
  have hstable : (prefixWord ++ tailWord_4309974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4309974).length < 2 ^ (prefixWord ++ tailWord_4309974).sum := by decide
  have hdescent : baseEnd_4309974 < baseStart_4309974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4309974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310103 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_4310103 : Nat := 118140960795 + 4310103 * 2 ^ 59
def prefixEnd_4310103 : Nat := 4983230072969 + 3 ^ 40 * 4310103 * 2
def baseEnd_4310103 : Nat := 2213154509385655435890703

theorem tailTrace_4310103 : CollatzResearch.WordTrace tailWord_4310103 prefixEnd_4310103 2213154509385655435890703 := by
  unfold tailWord_4310103
  simp only [CollatzResearch.WordTrace]
  refine ⟨157202371104240412833038963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104801580736160275222025975 157202371104240412833038963)
  ·
    refine ⟨235803556656360619249558445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157202371104240412833038963 235803556656360619249558445)
    ·
      refine ⟨88426333746135232218584417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235803556656360619249558445 88426333746135232218584417)
      ·
        refine ⟨66319750309601424163938313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88426333746135232218584417 66319750309601424163938313)
        ·
          refine ⟨49739812732201068122953735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66319750309601424163938313 49739812732201068122953735)
          ·
            refine ⟨74609719098301602184430603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49739812732201068122953735 74609719098301602184430603)
            ·
              refine ⟨111914578647452403276645905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74609719098301602184430603 111914578647452403276645905)
              ·
                refine ⟨83935933985589302457484429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111914578647452403276645905 83935933985589302457484429)
                ·
                  refine ⟨31475975244595988421556661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83935933985589302457484429 31475975244595988421556661)
                  ·
                    refine ⟨2950872679180873914520937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31475975244595988421556661 2950872679180873914520937)
                    ·
                      refine ⟨2213154509385655435890703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950872679180873914520937 2213154509385655435890703)
                      ·
                        rfl

theorem cell23_4310103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_4310103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310103 prefixEnd_4310103 := by exact prefixLift 4310103
  have htrace : WordTrace (prefixWord ++ tailWord_4310103) baseStart_4310103 baseEnd_4310103 := by
    simpa [prefixWord, tailWord_4310103, baseEnd_4310103] using wordTrace_append hprefix tailTrace_4310103
  have hstable : (prefixWord ++ tailWord_4310103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310103).length < 2 ^ (prefixWord ++ tailWord_4310103).sum := by decide
  have hdescent : baseEnd_4310103 < baseStart_4310103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310167 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_4310167 : Nat := 118140960795 + 4310167 * 2 ^ 59
def prefixEnd_4310167 : Nat := 4983230072969 + 3 ^ 40 * 4310167 * 2
def baseEnd_4310167 : Nat := 2213187372147543185490409

theorem tailTrace_4310167 : CollatzResearch.WordTrace tailWord_4310167 prefixEnd_4310167 2213187372147543185490409 := by
  unfold tailWord_4310167
  simp only [CollatzResearch.WordTrace]
  refine ⟨157204705376008551763368755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104803136917339034508912503 157204705376008551763368755)
  ·
    refine ⟨235807058064012827645053133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157204705376008551763368755 235807058064012827645053133)
    ·
      refine ⟨88427646774004810366894925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235807058064012827645053133 88427646774004810366894925)
      ·
        refine ⟨33160367540251803887585597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88427646774004810366894925 33160367540251803887585597)
        ·
          refine ⟨12435137827594426457844599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33160367540251803887585597 12435137827594426457844599)
          ·
            refine ⟨18652706741391639686766899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435137827594426457844599 18652706741391639686766899)
            ·
              refine ⟨27979060112087459530150349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18652706741391639686766899 27979060112087459530150349)
              ·
                refine ⟨10492147542032797323806381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27979060112087459530150349 10492147542032797323806381)
                ·
                  refine ⟨3934555328262298996427393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10492147542032797323806381 3934555328262298996427393)
                  ·
                    refine ⟨2950916496196724247320545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934555328262298996427393 2950916496196724247320545)
                    ·
                      refine ⟨2213187372147543185490409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950916496196724247320545 2213187372147543185490409)
                      ·
                        rfl

theorem cell23_4310167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_4310167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310167 prefixEnd_4310167 := by exact prefixLift 4310167
  have htrace : WordTrace (prefixWord ++ tailWord_4310167) baseStart_4310167 baseEnd_4310167 := by
    simpa [prefixWord, tailWord_4310167, baseEnd_4310167] using wordTrace_append hprefix tailTrace_4310167
  have hstable : (prefixWord ++ tailWord_4310167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310167).length < 2 ^ (prefixWord ++ tailWord_4310167).sum := by decide
  have hdescent : baseEnd_4310167 < baseStart_4310167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310170 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4310170 : Nat := 118140960795 + 4310170 * 2 ^ 59
def prefixEnd_4310170 : Nat := 4983230072969 + 3 ^ 40 * 4310170 * 2
def baseEnd_4310170 : Nat := 2213188912589506673752895

theorem tailTrace_4310170 : CollatzResearch.WordTrace tailWord_4310170 prefixEnd_4310170 2213188912589506673752895 := by
  unfold tailWord_4310170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39301203698749420818931991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104803209863331788850485309 39301203698749420818931991)
  ·
    refine ⟨58951805548124131228397987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39301203698749420818931991 58951805548124131228397987)
    ·
      refine ⟨88427708322186196842596981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58951805548124131228397987 88427708322186196842596981)
      ·
        refine ⟨8290097655204955953993467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88427708322186196842596981 8290097655204955953993467)
        ·
          refine ⟨12435146482807433930990201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8290097655204955953993467 12435146482807433930990201)
          ·
            refine ⟨9326359862105575448242651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12435146482807433930990201 9326359862105575448242651)
            ·
              refine ⟨13989539793158363172363977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9326359862105575448242651 13989539793158363172363977)
              ·
                refine ⟨10492154844868772379272983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13989539793158363172363977 10492154844868772379272983)
                ·
                  refine ⟨15738232267303158568909475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10492154844868772379272983 15738232267303158568909475)
                  ·
                    refine ⟨23607348400954737853364213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15738232267303158568909475 23607348400954737853364213)
                    ·
                      refine ⟨2213188912589506673752895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23607348400954737853364213 2213188912589506673752895)
                      ·
                        rfl

theorem cell23_4310170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4310170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310170 prefixEnd_4310170 := by exact prefixLift 4310170
  have htrace : WordTrace (prefixWord ++ tailWord_4310170) baseStart_4310170 baseEnd_4310170 := by
    simpa [prefixWord, tailWord_4310170, baseEnd_4310170] using wordTrace_append hprefix tailTrace_4310170
  have hstable : (prefixWord ++ tailWord_4310170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310170).length < 2 ^ (prefixWord ++ tailWord_4310170).sum := by decide
  have hdescent : baseEnd_4310170 < baseStart_4310170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310177 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 2, 4]
def baseStart_4310177 : Nat := 118140960795 + 4310177 * 2 ^ 59
def prefixEnd_4310177 : Nat := 4983230072969 + 3 ^ 40 * 4310177 * 2
def baseEnd_4310177 : Nat := 737730835651362715455121

theorem tailTrace_4310177 : CollatzResearch.WordTrace tailWord_4310177 prefixEnd_4310177 737730835651362715455121 := by
  unfold tailWord_4310177
  simp only [CollatzResearch.WordTrace]
  refine ⟨157205070105972323471232785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104803380070648215647488523 157205070105972323471232785)
  ·
    refine ⟨117903802579479242603424589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157205070105972323471232785 117903802579479242603424589)
    ·
      refine ⟨44213925967304715976284221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117903802579479242603424589 44213925967304715976284221)
      ·
        refine ⟨16580222237739268491106583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44213925967304715976284221 16580222237739268491106583)
        ·
          refine ⟨24870333356608902736659875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16580222237739268491106583 24870333356608902736659875)
          ·
            refine ⟨37305500034913354104989813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24870333356608902736659875 37305500034913354104989813)
            ·
              refine ⟨3497390628273126947342795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37305500034913354104989813 3497390628273126947342795)
              ·
                refine ⟨5246085942409690421014193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497390628273126947342795 5246085942409690421014193)
                ·
                  refine ⟨3934564456807267815760645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5246085942409690421014193 3934564456807267815760645)
                  ·
                    refine ⟨737730835651362715455121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3934564456807267815760645 737730835651362715455121)
                    ·
                      rfl

theorem cell23_4310177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_4310177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310177 prefixEnd_4310177 := by exact prefixLift 4310177
  have htrace : WordTrace (prefixWord ++ tailWord_4310177) baseStart_4310177 baseEnd_4310177 := by
    simpa [prefixWord, tailWord_4310177, baseEnd_4310177] using wordTrace_append hprefix tailTrace_4310177
  have hstable : (prefixWord ++ tailWord_4310177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310177).length < 2 ^ (prefixWord ++ tailWord_4310177).sum := by decide
  have hdescent : baseEnd_4310177 < baseStart_4310177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310180 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_4310180 : Nat := 118140960795 + 4310180 * 2 ^ 59
def prefixEnd_4310180 : Nat := 4983230072969 + 3 ^ 40 * 4310180 * 2
def baseEnd_4310180 : Nat := 2213194047396051634627849

theorem tailTrace_4310180 : CollatzResearch.WordTrace tailWord_4310180 prefixEnd_4310180 2213194047396051634627849 := by
  unfold tailWord_4310180
  simp only [CollatzResearch.WordTrace]
  refine ⟨78602589762480727491795997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104803453016640969989061329 78602589762480727491795997)
  ·
    refine ⟨29475971160930272809423499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78602589762480727491795997 29475971160930272809423499)
    ·
      refine ⟨44213956741395409214135249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29475971160930272809423499 44213956741395409214135249)
      ·
        refine ⟨33160467556046556910601437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44213956741395409214135249 33160467556046556910601437)
        ·
          refine ⟨12435175333517458841475539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33160467556046556910601437 12435175333517458841475539)
          ·
            refine ⟨18652763000276188262213309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435175333517458841475539 18652763000276188262213309)
            ·
              refine ⟨6994786125103570598329991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18652763000276188262213309 6994786125103570598329991)
              ·
                refine ⟨10492179187655355897494987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994786125103570598329991 10492179187655355897494987)
                ·
                  refine ⟨15738268781483033846242481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10492179187655355897494987 15738268781483033846242481)
                  ·
                    refine ⟨11803701586112275384681861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15738268781483033846242481 11803701586112275384681861)
                    ·
                      refine ⟨2213194047396051634627849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11803701586112275384681861 2213194047396051634627849)
                      ·
                        rfl

theorem cell23_4310180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_4310180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310180 prefixEnd_4310180 := by exact prefixLift 4310180
  have htrace : WordTrace (prefixWord ++ tailWord_4310180) baseStart_4310180 baseEnd_4310180 := by
    simpa [prefixWord, tailWord_4310180, baseEnd_4310180] using wordTrace_append hprefix tailTrace_4310180
  have hstable : (prefixWord ++ tailWord_4310180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310180).length < 2 ^ (prefixWord ++ tailWord_4310180).sum := by decide
  have hdescent : baseEnd_4310180 < baseStart_4310180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310201 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4310201 : Nat := 118140960795 + 4310201 * 2 ^ 59
def prefixEnd_4310201 : Nat := 4983230072969 + 3 ^ 40 * 4310201 * 2
def baseEnd_4310201 : Nat := 2213204830489796052465253

theorem tailTrace_4310201 : CollatzResearch.WordTrace tailWord_4310201 prefixEnd_4310201 2213204830489796052465253 := by
  unfold tailWord_4310201
  simp only [CollatzResearch.WordTrace]
  refine ⟨157205945457885375570106457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104803963638590250380070971 157205945457885375570106457)
  ·
    refine ⟨117904459093414031677579843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157205945457885375570106457 117904459093414031677579843)
    ·
      refine ⟨176856688640121047516369765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117904459093414031677579843 176856688640121047516369765)
      ·
        refine ⟨33160629120022696409319331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176856688640121047516369765 33160629120022696409319331)
        ·
          refine ⟨49740943680034044613978997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33160629120022696409319331 49740943680034044613978997)
          ·
            refine ⟨4663213470003191682560531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49740943680034044613978997 4663213470003191682560531)
            ·
              refine ⟨6994820205004787523840797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663213470003191682560531 6994820205004787523840797)
              ·
                refine ⟨2623057576876795321440299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6994820205004787523840797 2623057576876795321440299)
                ·
                  refine ⟨3934586365315192982160449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623057576876795321440299 3934586365315192982160449)
                  ·
                    refine ⟨2950939773986394736620337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934586365315192982160449 2950939773986394736620337)
                    ·
                      refine ⟨2213204830489796052465253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2950939773986394736620337 2213204830489796052465253)
                      ·
                        rfl

theorem cell23_4310201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4310201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310201 prefixEnd_4310201 := by exact prefixLift 4310201
  have htrace : WordTrace (prefixWord ++ tailWord_4310201) baseStart_4310201 baseEnd_4310201 := by
    simpa [prefixWord, tailWord_4310201, baseEnd_4310201] using wordTrace_append hprefix tailTrace_4310201
  have hstable : (prefixWord ++ tailWord_4310201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310201).length < 2 ^ (prefixWord ++ tailWord_4310201).sum := by decide
  have hdescent : baseEnd_4310201 < baseStart_4310201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310228 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_4310228 : Nat := 118140960795 + 4310228 * 2 ^ 59
def prefixEnd_4310228 : Nat := 4983230072969 + 3 ^ 40 * 4310228 * 2
def baseEnd_4310228 : Nat := 737739564822489148942543

theorem tailTrace_4310228 : CollatzResearch.WordTrace tailWord_4310228 prefixEnd_4310228 737739564822489148942543 := by
  unfold tailWord_4310228
  simp only [CollatzResearch.WordTrace]
  refine ⟨78603465114393779590669669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104804620152525039454226225 78603465114393779590669669)
  ·
    refine ⟨14738149708948833673250563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78603465114393779590669669 14738149708948833673250563)
    ·
      refine ⟨22107224563423250509875845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14738149708948833673250563 22107224563423250509875845)
      ·
        refine ⟨4145104605641859470601721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22107224563423250509875845 4145104605641859470601721)
        ·
          refine ⟨3108828454231394602951291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4145104605641859470601721 3108828454231394602951291)
          ·
            refine ⟨4663242681347091904426937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108828454231394602951291 4663242681347091904426937)
            ·
              refine ⟨3497432011010318928320203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663242681347091904426937 3497432011010318928320203)
              ·
                refine ⟨5246148016515478392480305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497432011010318928320203 5246148016515478392480305)
                ·
                  refine ⟨3934611012386608794360229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5246148016515478392480305 3934611012386608794360229)
                  ·
                    refine ⟨737739564822489148942543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3934611012386608794360229 737739564822489148942543)
                    ·
                      rfl

theorem cell23_4310228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_4310228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310228 prefixEnd_4310228 := by exact prefixLift 4310228
  have htrace : WordTrace (prefixWord ++ tailWord_4310228) baseStart_4310228 baseEnd_4310228 := by
    simpa [prefixWord, tailWord_4310228, baseEnd_4310228] using wordTrace_append hprefix tailTrace_4310228
  have hstable : (prefixWord ++ tailWord_4310228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310228).length < 2 ^ (prefixWord ++ tailWord_4310228).sum := by decide
  have hdescent : baseEnd_4310228 < baseStart_4310228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310293 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_4310293 : Nat := 118140960795 + 4310293 * 2 ^ 59
def prefixEnd_4310293 : Nat := 4983230072969 + 3 ^ 40 * 4310293 * 2
def baseEnd_4310293 : Nat := 737750690236669897504943

theorem tailTrace_4310293 : CollatzResearch.WordTrace tailWord_4310293 prefixEnd_4310293 737750690236669897504943 := by
  unfold tailWord_4310293
  simp only [CollatzResearch.WordTrace]
  refine ⟨157209300973552075282455533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104806200649034716854970355 157209300973552075282455533)
  ·
    refine ⟨58953487865082028230920825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157209300973552075282455533 58953487865082028230920825)
    ·
      refine ⟨44215115898811521173190619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58953487865082028230920825 44215115898811521173190619)
      ·
        refine ⟨66322673848217281759785929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44215115898811521173190619 66322673848217281759785929)
        ·
          refine ⟨49742005386162961319839447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66322673848217281759785929 49742005386162961319839447)
          ·
            refine ⟨74613008079244441979759171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49742005386162961319839447 74613008079244441979759171)
            ·
              refine ⟨111919512118866662969638757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74613008079244441979759171 111919512118866662969638757)
              ·
                refine ⟨20984908522287499306807267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111919512118866662969638757 20984908522287499306807267)
                ·
                  refine ⟨31477362783431248960210901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20984908522287499306807267 31477362783431248960210901)
                  ·
                    refine ⟨737750690236669897504943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31477362783431248960210901 737750690236669897504943)
                    ·
                      rfl

theorem cell23_4310293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_4310293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310293 prefixEnd_4310293 := by exact prefixLift 4310293
  have htrace : WordTrace (prefixWord ++ tailWord_4310293) baseStart_4310293 baseEnd_4310293 := by
    simpa [prefixWord, tailWord_4310293, baseEnd_4310293] using wordTrace_append hprefix tailTrace_4310293
  have hstable : (prefixWord ++ tailWord_4310293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310293).length < 2 ^ (prefixWord ++ tailWord_4310293).sum := by decide
  have hdescent : baseEnd_4310293 < baseStart_4310293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310314 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_4310314 : Nat := 118140960795 + 4310314 * 2 ^ 59
def prefixEnd_4310314 : Nat := 4983230072969 + 3 ^ 40 * 4310314 * 2
def baseEnd_4310314 : Nat := 245918094867083790039137

theorem tailTrace_4310314 : CollatzResearch.WordTrace tailWord_4310314 prefixEnd_4310314 245918094867083790039137 := by
  unfold tailWord_4310314
  simp only [CollatzResearch.WordTrace]
  refine ⟨39302516726618998967242499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104806711270983997245979997 39302516726618998967242499)
  ·
    refine ⟨58953775089928498450863749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39302516726618998967242499 58953775089928498450863749)
    ·
      refine ⟨11053832829361593459536953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58953775089928498450863749 11053832829361593459536953)
      ·
        refine ⟨8290374622021195094652715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11053832829361593459536953 8290374622021195094652715)
        ·
          refine ⟨12435561933031792641979073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8290374622021195094652715 12435561933031792641979073)
          ·
            refine ⟨9326671449773844481484305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12435561933031792641979073 9326671449773844481484305)
            ·
              refine ⟨6995003587330383361113229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9326671449773844481484305 6995003587330383361113229)
              ·
                refine ⟨2623126345248893760417461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6995003587330383361113229 2623126345248893760417461)
                ·
                  refine ⟨245918094867083790039137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623126345248893760417461 245918094867083790039137)
                  ·
                    rfl

theorem cell23_4310314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_4310314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310314 prefixEnd_4310314 := by exact prefixLift 4310314
  have htrace : WordTrace (prefixWord ++ tailWord_4310314) baseStart_4310314 baseEnd_4310314 := by
    simpa [prefixWord, tailWord_4310314, baseEnd_4310314] using wordTrace_append hprefix tailTrace_4310314
  have hstable : (prefixWord ++ tailWord_4310314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310314).length < 2 ^ (prefixWord ++ tailWord_4310314).sum := by decide
  have hdescent : baseEnd_4310314 < baseStart_4310314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310330 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_4310330 : Nat := 118140960795 + 4310330 * 2 ^ 59
def prefixEnd_4310330 : Nat := 4983230072969 + 3 ^ 40 * 4310330 * 2
def baseEnd_4310330 : Nat := 2213271069494226047752159

theorem tailTrace_4310330 : CollatzResearch.WordTrace tailWord_4310330 prefixEnd_4310330 2213271069494226047752159 := by
  unfold tailWord_4310330
  simp only [CollatzResearch.WordTrace]
  refine ⟨39302662618604507650388111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104807100316278687067701629 39302662618604507650388111)
  ·
    refine ⟨58953993927906761475582167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39302662618604507650388111 58953993927906761475582167)
    ·
      refine ⟨88430990891860142213373251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58953993927906761475582167 88430990891860142213373251)
      ·
        refine ⟨132646486337790213320059877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88430990891860142213373251 132646486337790213320059877)
        ·
          refine ⟨24871216188335664997511227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132646486337790213320059877 24871216188335664997511227)
          ·
            refine ⟨37306824282503497496266841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24871216188335664997511227 37306824282503497496266841)
            ·
              refine ⟨27980118211877623122200131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37306824282503497496266841 27980118211877623122200131)
              ·
                refine ⟨41970177317816434683300197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27980118211877623122200131 41970177317816434683300197)
                ·
                  refine ⟨7869408247090581503118787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41970177317816434683300197 7869408247090581503118787)
                  ·
                    refine ⟨11804112370635872254678181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7869408247090581503118787 11804112370635872254678181)
                    ·
                      refine ⟨2213271069494226047752159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11804112370635872254678181 2213271069494226047752159)
                      ·
                        rfl

theorem cell23_4310330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_4310330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310330 prefixEnd_4310330 := by exact prefixLift 4310330
  have htrace : WordTrace (prefixWord ++ tailWord_4310330) baseStart_4310330 baseEnd_4310330 := by
    simpa [prefixWord, tailWord_4310330, baseEnd_4310330] using wordTrace_append hprefix tailTrace_4310330
  have hstable : (prefixWord ++ tailWord_4310330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310330).length < 2 ^ (prefixWord ++ tailWord_4310330).sum := by decide
  have hdescent : baseEnd_4310330 < baseStart_4310330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310342 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4310342 : Nat := 118140960795 + 4310342 * 2 ^ 59
def prefixEnd_4310342 : Nat := 4983230072969 + 3 ^ 40 * 4310342 * 2
def baseEnd_4310342 : Nat := 2213277231262080000802105

theorem tailTrace_4310342 : CollatzResearch.WordTrace tailWord_4310342 prefixEnd_4310342 2213277231262080000802105 := by
  unfold tailWord_4310342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912846504699204895343415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104807392100249704433992853 4912846504699204895343415)
  ·
    refine ⟨7369269757048807343015123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4912846504699204895343415 7369269757048807343015123)
    ·
      refine ⟨11053904635573211014522685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369269757048807343015123 11053904635573211014522685)
      ·
        refine ⟨4145214238339954130446007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11053904635573211014522685 4145214238339954130446007)
        ·
          refine ⟨6217821357509931195669011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145214238339954130446007 6217821357509931195669011)
          ·
            refine ⟨9326732036264896793503517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217821357509931195669011 9326732036264896793503517)
            ·
              refine ⟨3497524513599336297563819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9326732036264896793503517 3497524513599336297563819)
              ·
                refine ⟨5246286770399004446345729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497524513599336297563819 5246286770399004446345729)
                ·
                  refine ⟨3934715077799253334759297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5246286770399004446345729 3934715077799253334759297)
                  ·
                    refine ⟨2951036308349440001069473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934715077799253334759297 2951036308349440001069473)
                    ·
                      refine ⟨2213277231262080000802105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951036308349440001069473 2213277231262080000802105)
                      ·
                        rfl

theorem cell23_4310342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4310342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310342 prefixEnd_4310342 := by exact prefixLift 4310342
  have htrace : WordTrace (prefixWord ++ tailWord_4310342) baseStart_4310342 baseEnd_4310342 := by
    simpa [prefixWord, tailWord_4310342, baseEnd_4310342] using wordTrace_append hprefix tailTrace_4310342
  have hstable : (prefixWord ++ tailWord_4310342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310342).length < 2 ^ (prefixWord ++ tailWord_4310342).sum := by decide
  have hdescent : baseEnd_4310342 < baseStart_4310342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310350 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_4310350 : Nat := 118140960795 + 4310350 * 2 ^ 59
def prefixEnd_4310350 : Nat := 4983230072969 + 3 ^ 40 * 4310350 * 2
def baseEnd_4310350 : Nat := 2213281339107315969502067

theorem tailTrace_4310350 : CollatzResearch.WordTrace tailWord_4310350 prefixEnd_4310350 2213281339107315969502067 := by
  unfold tailWord_4310350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19651422491793196752160063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104807586622897049344853669 19651422491793196752160063)
  ·
    refine ⟨29477133737689795128240095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19651422491793196752160063 29477133737689795128240095)
    ·
      refine ⟨44215700606534692692360143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29477133737689795128240095 44215700606534692692360143)
      ·
        refine ⟨66323550909802039038540215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44215700606534692692360143 66323550909802039038540215)
        ·
          refine ⟨99485326364703058557810323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66323550909802039038540215 99485326364703058557810323)
          ·
            refine ⟨149227989547054587836715485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99485326364703058557810323 149227989547054587836715485)
            ·
              refine ⟨55960496080145470438768307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149227989547054587836715485 55960496080145470438768307)
              ·
                refine ⟨83940744120218205658152461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55960496080145470438768307 83940744120218205658152461)
                ·
                  refine ⟨31477779045081827121807173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83940744120218205658152461 31477779045081827121807173)
                  ·
                    refine ⟨5902083570952842585338845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31477779045081827121807173 5902083570952842585338845)
                    ·
                      refine ⟨2213281339107315969502067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5902083570952842585338845 2213281339107315969502067)
                      ·
                        rfl

theorem cell23_4310350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_4310350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310350 prefixEnd_4310350 := by exact prefixLift 4310350
  have htrace : WordTrace (prefixWord ++ tailWord_4310350) baseStart_4310350 baseEnd_4310350 := by
    simpa [prefixWord, tailWord_4310350, baseEnd_4310350] using wordTrace_append hprefix tailTrace_4310350
  have hstable : (prefixWord ++ tailWord_4310350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310350).length < 2 ^ (prefixWord ++ tailWord_4310350).sum := by decide
  have hdescent : baseEnd_4310350 < baseStart_4310350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310357 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_4310357 : Nat := 118140960795 + 4310357 * 2 ^ 59
def prefixEnd_4310357 : Nat := 4983230072969 + 3 ^ 40 * 4310357 * 2
def baseEnd_4310357 : Nat := 737761644490632480704845

theorem tailTrace_4310357 : CollatzResearch.WordTrace tailWord_4310357 prefixEnd_4310357 737761644490632480704845 := by
  unfold tailWord_4310357
  simp only [CollatzResearch.WordTrace]
  refine ⟨157211635245320214212785325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104807756830213476141856883 157211635245320214212785325)
  ·
    refine ⟨58954363216995080329794497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157211635245320214212785325 58954363216995080329794497)
    ·
      refine ⟨44215772412746310247345873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58954363216995080329794497 44215772412746310247345873)
      ·
        refine ⟨33161829309559732685509405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44215772412746310247345873 33161829309559732685509405)
        ·
          refine ⟨12435685991084899757066027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33161829309559732685509405 12435685991084899757066027)
          ·
            refine ⟨18653528986627349635599041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435685991084899757066027 18653528986627349635599041)
            ·
              refine ⟨13990146739970512226699281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18653528986627349635599041 13990146739970512226699281)
              ·
                refine ⟨10492610054977884170024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13990146739970512226699281 10492610054977884170024461)
                ·
                  refine ⟨3934728770616706563759173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10492610054977884170024461 3934728770616706563759173)
                  ·
                    refine ⟨737761644490632480704845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3934728770616706563759173 737761644490632480704845)
                    ·
                      rfl

theorem cell23_4310357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_4310357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310357 prefixEnd_4310357 := by exact prefixLift 4310357
  have htrace : WordTrace (prefixWord ++ tailWord_4310357) baseStart_4310357 baseEnd_4310357 := by
    simpa [prefixWord, tailWord_4310357, baseEnd_4310357] using wordTrace_append hprefix tailTrace_4310357
  have hstable : (prefixWord ++ tailWord_4310357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310357).length < 2 ^ (prefixWord ++ tailWord_4310357).sum := by decide
  have hdescent : baseEnd_4310357 < baseStart_4310357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310365 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 5]
def baseStart_4310365 : Nat := 118140960795 + 4310365 * 2 ^ 59
def prefixEnd_4310365 : Nat := 4983230072969 + 3 ^ 40 * 4310365 * 2
def baseEnd_4310365 : Nat := 245921004590792601201611

theorem tailTrace_4310365 : CollatzResearch.WordTrace tailWord_4310365 prefixEnd_4310365 245921004590792601201611 := by
  unfold tailWord_4310365
  simp only [CollatzResearch.WordTrace]
  refine ⟨157211927029291231579076549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104807951352860821052717699 157211927029291231579076549)
  ·
    refine ⟨29477236317992105921076853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157211927029291231579076549 29477236317992105921076853)
    ·
      refine ⟨2763490904811759930100955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29477236317992105921076853 2763490904811759930100955)
      ·
        refine ⟨4145236357217639895151433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763490904811759930100955 4145236357217639895151433)
        ·
          refine ⟨3108927267913229921363575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4145236357217639895151433 3108927267913229921363575)
          ·
            refine ⟨4663390901869844882045363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108927267913229921363575 4663390901869844882045363)
            ·
              refine ⟨6995086352804767323068045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663390901869844882045363 6995086352804767323068045)
              ·
                refine ⟨2623157382301787746150517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6995086352804767323068045 2623157382301787746150517)
                ·
                  refine ⟨245921004590792601201611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623157382301787746150517 245921004590792601201611)
                  ·
                    rfl

theorem cell23_4310365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_4310365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310365 prefixEnd_4310365 := by exact prefixLift 4310365
  have htrace : WordTrace (prefixWord ++ tailWord_4310365) baseStart_4310365 baseEnd_4310365 := by
    simpa [prefixWord, tailWord_4310365, baseEnd_4310365] using wordTrace_append hprefix tailTrace_4310365
  have hstable : (prefixWord ++ tailWord_4310365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310365).length < 2 ^ (prefixWord ++ tailWord_4310365).sum := by decide
  have hdescent : baseEnd_4310365 < baseStart_4310365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310370 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_4310370 : Nat := 118140960795 + 4310370 * 2 ^ 59
def prefixEnd_4310370 : Nat := 4983230072969 + 3 ^ 40 * 4310370 * 2
def baseEnd_4310370 : Nat := 245921289857822876805775

theorem tailTrace_4310370 : CollatzResearch.WordTrace tailWord_4310370 prefixEnd_4310370 245921289857822876805775 := by
  unfold tailWord_4310370
  simp only [CollatzResearch.WordTrace]
  refine ⟨39303027348568279358252141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104808072929515411622005709 39303027348568279358252141)
  ·
    refine ⟨14738635255713104759344553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39303027348568279358252141 14738635255713104759344553)
    ·
      refine ⟨11053976441784828569508415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14738635255713104759344553 11053976441784828569508415)
      ·
        refine ⟨16580964662677242854262623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11053976441784828569508415 16580964662677242854262623)
        ·
          refine ⟨24871446994015864281393935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16580964662677242854262623 24871446994015864281393935)
          ·
            refine ⟨37307170491023796422090903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24871446994015864281393935 37307170491023796422090903)
            ·
              refine ⟨55960755736535694633136355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37307170491023796422090903 55960755736535694633136355)
              ·
                refine ⟨83941133604803541949704533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55960755736535694633136355 83941133604803541949704533)
                ·
                  refine ⟨245921289857822876805775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83941133604803541949704533 245921289857822876805775)
                  ·
                    rfl

theorem cell23_4310370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_4310370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310370 prefixEnd_4310370 := by exact prefixLift 4310370
  have htrace : WordTrace (prefixWord ++ tailWord_4310370) baseStart_4310370 baseEnd_4310370 := by
    simpa [prefixWord, tailWord_4310370, baseEnd_4310370] using wordTrace_append hprefix tailTrace_4310370
  have hstable : (prefixWord ++ tailWord_4310370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310370).length < 2 ^ (prefixWord ++ tailWord_4310370).sum := by decide
  have hdescent : baseEnd_4310370 < baseStart_4310370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310404 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 6]
def baseStart_4310404 : Nat := 118140960795 + 4310404 * 2 ^ 59
def prefixEnd_4310404 : Nat := 4983230072969 + 3 ^ 40 * 4310404 * 2
def baseEnd_4310404 : Nat := 245923229673628750914091

theorem tailTrace_4310404 : CollatzResearch.WordTrace tailWord_4310404 prefixEnd_4310404 245923229673628750914091 := by
  unfold tailWord_4310404
  simp only [CollatzResearch.WordTrace]
  refine ⟨78606674738074970619873133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104808899650766627493164177 78606674738074970619873133)
  ·
    refine ⟨29477503026778113982452425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78606674738074970619873133 29477503026778113982452425)
    ·
      refine ⟨22108127270083585486839319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29477503026778113982452425 22108127270083585486839319)
      ·
        refine ⟨33162190905125378230258979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22108127270083585486839319 33162190905125378230258979)
        ·
          refine ⟨49743286357688067345388469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33162190905125378230258979 49743286357688067345388469)
          ·
            refine ⟨4663433096033256313630169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49743286357688067345388469 4663433096033256313630169)
            ·
              refine ⟨3497574822024942235222627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663433096033256313630169 3497574822024942235222627)
              ·
                refine ⟨5246362233037413352833941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497574822024942235222627 5246362233037413352833941)
                ·
                  refine ⟨245923229673628750914091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5246362233037413352833941 245923229673628750914091)
                  ·
                    rfl

theorem cell23_4310404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_4310404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310404 prefixEnd_4310404 := by exact prefixLift 4310404
  have htrace : WordTrace (prefixWord ++ tailWord_4310404) baseStart_4310404 baseEnd_4310404 := by
    simpa [prefixWord, tailWord_4310404, baseEnd_4310404] using wordTrace_append hprefix tailTrace_4310404
  have hstable : (prefixWord ++ tailWord_4310404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310404).length < 2 ^ (prefixWord ++ tailWord_4310404).sum := by decide
  have hdescent : baseEnd_4310404 < baseStart_4310404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310450 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_4310450 : Nat := 118140960795 + 4310450 * 2 ^ 59
def prefixEnd_4310450 : Nat := 4983230072969 + 3 ^ 40 * 4310450 * 2
def baseEnd_4310450 : Nat := 2213332687172765578251607

theorem tailTrace_4310450 : CollatzResearch.WordTrace tailWord_4310450 prefixEnd_4310450 2213332687172765578251607 := by
  unfold tailWord_4310450
  simp only [CollatzResearch.WordTrace]
  refine ⟨39303756808495822773980201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104810018155988860730613869 39303756808495822773980201)
  ·
    refine ⟨29477817606371867080485151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39303756808495822773980201 29477817606371867080485151)
    ·
      refine ⟨44216726409557800620727727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29477817606371867080485151 44216726409557800620727727)
      ·
        refine ⟨66325089614336700931091591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44216726409557800620727727 66325089614336700931091591)
        ·
          refine ⟨99487634421505051396637387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66325089614336700931091591 99487634421505051396637387)
          ·
            refine ⟨149231451632257577094956081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99487634421505051396637387 149231451632257577094956081)
            ·
              refine ⟨111923588724193182821217061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149231451632257577094956081 111923588724193182821217061)
              ·
                refine ⟨20985672885786221778978199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111923588724193182821217061 20985672885786221778978199)
                ·
                  refine ⟨31478509328679332668467299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20985672885786221778978199 31478509328679332668467299)
                  ·
                    refine ⟨47217763993018999002700949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31478509328679332668467299 47217763993018999002700949)
                    ·
                      refine ⟨2213332687172765578251607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47217763993018999002700949 2213332687172765578251607)
                      ·
                        rfl

theorem cell23_4310450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_4310450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310450 prefixEnd_4310450 := by exact prefixLift 4310450
  have htrace : WordTrace (prefixWord ++ tailWord_4310450) baseStart_4310450 baseEnd_4310450 := by
    simpa [prefixWord, tailWord_4310450, baseEnd_4310450] using wordTrace_append hprefix tailTrace_4310450
  have hstable : (prefixWord ++ tailWord_4310450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310450).length < 2 ^ (prefixWord ++ tailWord_4310450).sum := by decide
  have hdescent : baseEnd_4310450 < baseStart_4310450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310504 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4310504 : Nat := 118140960795 + 4310504 * 2 ^ 59
def prefixEnd_4310504 : Nat := 4983230072969 + 3 ^ 40 * 4310504 * 2
def baseEnd_4310504 : Nat := 2213360415128108366976359

theorem tailTrace_4310504 : CollatzResearch.WordTrace tailWord_4310504 prefixEnd_4310504 2213360415128108366976359 := by
  unfold tailWord_4310504
  simp only [CollatzResearch.WordTrace]
  refine ⟨78608498387893829159193283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104811331183858438878924377 78608498387893829159193283)
  ·
    refine ⟨117912747581840743738789925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78608498387893829159193283 117912747581840743738789925)
    ·
      refine ⟨22108640171595139451023111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117912747581840743738789925 22108640171595139451023111)
      ·
        refine ⟨33162960257392709176534667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22108640171595139451023111 33162960257392709176534667)
        ·
          refine ⟨49744440386089063764802001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33162960257392709176534667 49744440386089063764802001)
          ·
            refine ⟨37308330289566797823601501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49744440386089063764802001 37308330289566797823601501)
            ·
              refine ⟨13990623858587549183850563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37308330289566797823601501 13990623858587549183850563)
              ·
                refine ⟨20985935787881323775775845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13990623858587549183850563 20985935787881323775775845)
                ·
                  refine ⟨3934862960227748207957971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20985935787881323775775845 3934862960227748207957971)
                  ·
                    refine ⟨5902294440341622311936957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3934862960227748207957971 5902294440341622311936957)
                    ·
                      refine ⟨2213360415128108366976359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5902294440341622311936957 2213360415128108366976359)
                      ·
                        rfl

theorem cell23_4310504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4310504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310504 prefixEnd_4310504 := by exact prefixLift 4310504
  have htrace : WordTrace (prefixWord ++ tailWord_4310504) baseStart_4310504 baseEnd_4310504 := by
    simpa [prefixWord, tailWord_4310504, baseEnd_4310504] using wordTrace_append hprefix tailTrace_4310504
  have hstable : (prefixWord ++ tailWord_4310504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310504).length < 2 ^ (prefixWord ++ tailWord_4310504).sum := by decide
  have hdescent : baseEnd_4310504 < baseStart_4310504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310547 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5]
def baseStart_4310547 : Nat := 118140960795 + 4310547 * 2 ^ 59
def prefixEnd_4310547 : Nat := 4983230072969 + 3 ^ 40 * 4310547 * 2
def baseEnd_4310547 : Nat := 2213382494796251698738661

theorem tailTrace_4310547 : CollatzResearch.WordTrace tailWord_4310547 prefixEnd_4310547 2213382494796251698738661 := by
  unfold tailWord_4310547
  simp only [CollatzResearch.WordTrace]
  refine ⟨157218565114631876662201895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104812376743087917774801263 157218565114631876662201895)
  ·
    refine ⟨235827847671947814993302843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157218565114631876662201895 235827847671947814993302843)
    ·
      refine ⟨353741771507921722489954265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235827847671947814993302843 353741771507921722489954265)
      ·
        refine ⟨265306328630941291867465699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353741771507921722489954265 265306328630941291867465699)
        ·
          refine ⟨397959492946411937801198549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265306328630941291867465699 397959492946411937801198549)
          ·
            refine ⟨9327175615931529792215591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 397959492946411937801198549 9327175615931529792215591)
            ·
              refine ⟨13990763423897294688323387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9327175615931529792215591 13990763423897294688323387)
              ·
                refine ⟨20986145135845942032485081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13990763423897294688323387 20986145135845942032485081)
                ·
                  refine ⟨15739608851884456524363811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20986145135845942032485081 15739608851884456524363811)
                  ·
                    refine ⟨23609413277826684786545717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15739608851884456524363811 23609413277826684786545717)
                    ·
                      refine ⟨2213382494796251698738661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23609413277826684786545717 2213382494796251698738661)
                      ·
                        rfl

theorem cell23_4310547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_4310547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310547 prefixEnd_4310547 := by exact prefixLift 4310547
  have htrace : WordTrace (prefixWord ++ tailWord_4310547) baseStart_4310547 baseEnd_4310547 := by
    simpa [prefixWord, tailWord_4310547, baseEnd_4310547] using wordTrace_append hprefix tailTrace_4310547
  have hstable : (prefixWord ++ tailWord_4310547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310547).length < 2 ^ (prefixWord ++ tailWord_4310547).sum := by decide
  have hdescent : baseEnd_4310547 < baseStart_4310547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310561 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_4310561 : Nat := 118140960795 + 4310561 * 2 ^ 59
def prefixEnd_4310561 : Nat := 4983230072969 + 3 ^ 40 * 4310561 * 2
def baseEnd_4310561 : Nat := 2213389683525414643963597

theorem tailTrace_4310561 : CollatzResearch.WordTrace tailWord_4310561 prefixEnd_4310561 2213389683525414643963597 := by
  unfold tailWord_4310561
  simp only [CollatzResearch.WordTrace]
  refine ⟨157219075736581157053211537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104812717157720771368807691 157219075736581157053211537)
  ·
    refine ⟨117914306802435867789908653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157219075736581157053211537 117914306802435867789908653)
    ·
      refine ⟨44217865050913450421215745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117914306802435867789908653 44217865050913450421215745)
      ·
        refine ⟨33163398788185087815911809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44217865050913450421215745 33163398788185087815911809)
        ·
          refine ⟨24872549091138815861933857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33163398788185087815911809 24872549091138815861933857)
          ·
            refine ⟨18654411818354111896450393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24872549091138815861933857 18654411818354111896450393)
            ·
              refine ⟨13990808863765583922337795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18654411818354111896450393 13990808863765583922337795)
              ·
                refine ⟨20986213295648375883506693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13990808863765583922337795 20986213295648375883506693)
                ·
                  refine ⟨3934914992934070478157505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20986213295648375883506693 3934914992934070478157505)
                  ·
                    refine ⟨2951186244700552858618129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934914992934070478157505 2951186244700552858618129)
                    ·
                      refine ⟨2213389683525414643963597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951186244700552858618129 2213389683525414643963597)
                      ·
                        rfl

theorem cell23_4310561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_4310561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310561 prefixEnd_4310561 := by exact prefixLift 4310561
  have htrace : WordTrace (prefixWord ++ tailWord_4310561) baseStart_4310561 baseEnd_4310561 := by
    simpa [prefixWord, tailWord_4310561, baseEnd_4310561] using wordTrace_append hprefix tailTrace_4310561
  have hstable : (prefixWord ++ tailWord_4310561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310561).length < 2 ^ (prefixWord ++ tailWord_4310561).sum := by decide
  have hdescent : baseEnd_4310561 < baseStart_4310561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310577 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_4310577 : Nat := 118140960795 + 4310577 * 2 ^ 59
def prefixEnd_4310577 : Nat := 4983230072969 + 3 ^ 40 * 4310577 * 2
def baseEnd_4310577 : Nat := 2213397899215886581363523

theorem tailTrace_4310577 : CollatzResearch.WordTrace tailWord_4310577 prefixEnd_4310577 2213397899215886581363523 := by
  unfold tailWord_4310577
  simp only [CollatzResearch.WordTrace]
  refine ⟨157219659304523191785793985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104813106203015461190529323 157219659304523191785793985)
  ·
    refine ⟨117914744478392393839345489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157219659304523191785793985 117914744478392393839345489)
    ·
      refine ⟨88436058358794295379509117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117914744478392393839345489 88436058358794295379509117)
      ·
        refine ⟨33163521884547860767315919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88436058358794295379509117 33163521884547860767315919)
        ·
          refine ⟨49745282826821791150973879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33163521884547860767315919 49745282826821791150973879)
          ·
            refine ⟨74617924240232686726460819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49745282826821791150973879 74617924240232686726460819)
            ·
              refine ⟨111926886360349030089691229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74617924240232686726460819 111926886360349030089691229)
              ·
                refine ⟨41972582385130886283634211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111926886360349030089691229 41972582385130886283634211)
                ·
                  refine ⟨62958873577696329425451317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41972582385130886283634211 62958873577696329425451317)
                  ·
                    refine ⟨5902394397909030883636061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62958873577696329425451317 5902394397909030883636061)
                    ·
                      refine ⟨2213397899215886581363523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5902394397909030883636061 2213397899215886581363523)
                      ·
                        rfl

theorem cell23_4310577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_4310577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310577 prefixEnd_4310577 := by exact prefixLift 4310577
  have htrace : WordTrace (prefixWord ++ tailWord_4310577) baseStart_4310577 baseEnd_4310577 := by
    simpa [prefixWord, tailWord_4310577, baseEnd_4310577] using wordTrace_append hprefix tailTrace_4310577
  have hstable : (prefixWord ++ tailWord_4310577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310577).length < 2 ^ (prefixWord ++ tailWord_4310577).sum := by decide
  have hdescent : baseEnd_4310577 < baseStart_4310577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310582 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4310582 : Nat := 118140960795 + 4310582 * 2 ^ 59
def prefixEnd_4310582 : Nat := 4983230072969 + 3 ^ 40 * 4310582 * 2
def baseEnd_4310582 : Nat := 2213400466619159061801001

theorem tailTrace_4310582 : CollatzResearch.WordTrace tailWord_4310582 prefixEnd_4310582 2213400466619159061801001 := by
  unfold tailWord_4310582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9826240104344067352482875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104813227779670051759817333 9826240104344067352482875)
  ·
    refine ⟨14739360156516101028724313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9826240104344067352482875 14739360156516101028724313)
    ·
      refine ⟨11054520117387075771543235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14739360156516101028724313 11054520117387075771543235)
      ·
        refine ⟨16581780176080613657314853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11054520117387075771543235 16581780176080613657314853)
        ·
          refine ⟨3109083783015115060746535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16581780176080613657314853 3109083783015115060746535)
          ·
            refine ⟨4663625674522672591119803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109083783015115060746535 4663625674522672591119803)
            ·
              refine ⟨6995438511784008886679705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663625674522672591119803 6995438511784008886679705)
              ·
                refine ⟨5246578883838006665009779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6995438511784008886679705 5246578883838006665009779)
                ·
                  refine ⟨7869868325757009997514669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246578883838006665009779 7869868325757009997514669)
                  ·
                    refine ⟨2951200622158878749068001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7869868325757009997514669 2951200622158878749068001)
                    ·
                      refine ⟨2213400466619159061801001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951200622158878749068001 2213400466619159061801001)
                      ·
                        rfl

theorem cell23_4310582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4310582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310582 prefixEnd_4310582 := by exact prefixLift 4310582
  have htrace : WordTrace (prefixWord ++ tailWord_4310582) baseStart_4310582 baseEnd_4310582 := by
    simpa [prefixWord, tailWord_4310582, baseEnd_4310582] using wordTrace_append hprefix tailTrace_4310582
  have hstable : (prefixWord ++ tailWord_4310582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310582).length < 2 ^ (prefixWord ++ tailWord_4310582).sum := by decide
  have hdescent : baseEnd_4310582 < baseStart_4310582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310704 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_4310704 : Nat := 118140960795 + 4310704 * 2 ^ 59
def prefixEnd_4310704 : Nat := 4983230072969 + 3 ^ 40 * 4310704 * 2
def baseEnd_4310704 : Nat := 737821037086335861491813

theorem tailTrace_4310704 : CollatzResearch.WordTrace tailWord_4310704 prefixEnd_4310704 737821037086335861491813 := by
  unfold tailWord_4310704
  simp only [CollatzResearch.WordTrace]
  refine ⟨78612145687531546237833583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104816194250042061650444777 78612145687531546237833583)
  ·
    refine ⟨117918218531297319356750375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78612145687531546237833583 117918218531297319356750375)
    ·
      refine ⟨176877327796945979035125563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117918218531297319356750375 176877327796945979035125563)
      ·
        refine ⟨265315991695418968552688345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176877327796945979035125563 265315991695418968552688345)
        ·
          refine ⟨198986993771564226414516259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265315991695418968552688345 198986993771564226414516259)
          ·
            refine ⟨298480490657346339621774389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198986993771564226414516259 298480490657346339621774389)
            ·
              refine ⟨27982545999126219339541349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 298480490657346339621774389 27982545999126219339541349)
              ·
                refine ⟨5246727374836166126164003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27982545999126219339541349 5246727374836166126164003)
                ·
                  refine ⟨7870091062254249189246005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246727374836166126164003 7870091062254249189246005)
                  ·
                    refine ⟨737821037086335861491813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7870091062254249189246005 737821037086335861491813)
                    ·
                      rfl

theorem cell23_4310704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_4310704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310704 prefixEnd_4310704 := by exact prefixLift 4310704
  have htrace : WordTrace (prefixWord ++ tailWord_4310704) baseStart_4310704 baseEnd_4310704 := by
    simpa [prefixWord, tailWord_4310704, baseEnd_4310704] using wordTrace_append hprefix tailTrace_4310704
  have hstable : (prefixWord ++ tailWord_4310704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310704).length < 2 ^ (prefixWord ++ tailWord_4310704).sum := by decide
  have hdescent : baseEnd_4310704 < baseStart_4310704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310711 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_4310711 : Nat := 118140960795 + 4310711 * 2 ^ 59
def prefixEnd_4310711 : Nat := 4983230072969 + 3 ^ 40 * 4310711 * 2
def baseEnd_4310711 : Nat := 2213466705623589057087907

theorem tailTrace_4310711 : CollatzResearch.WordTrace tailWord_4310711 prefixEnd_4310711 2213466705623589057087907 := by
  unfold tailWord_4310711
  simp only [CollatzResearch.WordTrace]
  refine ⟨157224546686037732671171987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104816364457358488447447991 157224546686037732671171987)
  ·
    refine ⟨235836820029056599006757981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157224546686037732671171987 235836820029056599006757981)
    ·
      refine ⟨88438807510896224627534243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235836820029056599006757981 88438807510896224627534243)
      ·
        refine ⟨132658211266344336941301365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88438807510896224627534243 132658211266344336941301365)
        ·
          refine ⟨12436707306219781588247003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132658211266344336941301365 12436707306219781588247003)
          ·
            refine ⟨18655060959329672382370505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12436707306219781588247003 18655060959329672382370505)
            ·
              refine ⟨13991295719497254286777879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18655060959329672382370505 13991295719497254286777879)
              ·
                refine ⟨20986943579245881430166819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13991295719497254286777879 20986943579245881430166819)
                ·
                  refine ⟨31480415368868822145250229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20986943579245881430166819 31480415368868822145250229)
                  ·
                    refine ⟨2951288940831452076117209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31480415368868822145250229 2951288940831452076117209)
                    ·
                      refine ⟨2213466705623589057087907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951288940831452076117209 2213466705623589057087907)
                      ·
                        rfl

theorem cell23_4310711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_4310711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310711 prefixEnd_4310711 := by exact prefixLift 4310711
  have htrace : WordTrace (prefixWord ++ tailWord_4310711) baseStart_4310711 baseEnd_4310711 := by
    simpa [prefixWord, tailWord_4310711, baseEnd_4310711] using wordTrace_append hprefix tailTrace_4310711
  have hstable : (prefixWord ++ tailWord_4310711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310711).length < 2 ^ (prefixWord ++ tailWord_4310711).sum := by decide
  have hdescent : baseEnd_4310711 < baseStart_4310711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310722 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4310722 : Nat := 118140960795 + 4310722 * 2 ^ 59
def prefixEnd_4310722 : Nat := 4983230072969 + 3 ^ 40 * 4310722 * 2
def baseEnd_4310722 : Nat := 2213472353910788514050357

theorem tailTrace_4310722 : CollatzResearch.WordTrace tailWord_4310722 prefixEnd_4310722 2213472353910788514050357 := by
  unfold tailWord_4310722
  simp only [CollatzResearch.WordTrace]
  refine ⟨39306236972249470387455605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104816631925998587699881613 39306236972249470387455605)
  ·
    refine ⟨3684959716148387848823963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39306236972249470387455605 3684959716148387848823963)
    ·
      refine ⟨5527439574222581773235945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3684959716148387848823963 5527439574222581773235945)
      ·
        refine ⟨4145579680666936329926959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5527439574222581773235945 4145579680666936329926959)
        ·
          refine ⟨6218369521000404494890439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145579680666936329926959 6218369521000404494890439)
          ·
            refine ⟨9327554281500606742335659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218369521000404494890439 9327554281500606742335659)
            ·
              refine ⟨13991331422250910113503489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9327554281500606742335659 13991331422250910113503489)
              ·
                refine ⟨10493498566688182585127617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13991331422250910113503489 10493498566688182585127617)
                ·
                  refine ⟨7870123925016136938845713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10493498566688182585127617 7870123925016136938845713)
                  ·
                    refine ⟨5902592943762102704134285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7870123925016136938845713 5902592943762102704134285)
                    ·
                      refine ⟨2213472353910788514050357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5902592943762102704134285 2213472353910788514050357)
                      ·
                        rfl

theorem cell23_4310722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4310722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310722 prefixEnd_4310722 := by exact prefixLift 4310722
  have htrace : WordTrace (prefixWord ++ tailWord_4310722) baseStart_4310722 baseEnd_4310722 := by
    simpa [prefixWord, tailWord_4310722, baseEnd_4310722] using wordTrace_append hprefix tailTrace_4310722
  have hstable : (prefixWord ++ tailWord_4310722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310722).length < 2 ^ (prefixWord ++ tailWord_4310722).sum := by decide
  have hdescent : baseEnd_4310722 < baseStart_4310722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310742 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_4310742 : Nat := 118140960795 + 4310742 * 2 ^ 59
def prefixEnd_4310742 : Nat := 4983230072969 + 3 ^ 40 * 4310742 * 2
def baseEnd_4310742 : Nat := 245942513724875381755585

theorem tailTrace_4310742 : CollatzResearch.WordTrace tailWord_4310742 prefixEnd_4310742 245942513724875381755585 := by
  unfold tailWord_4310742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9826604834307839060346905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104817118232616949977033653 9826604834307839060346905)
  ·
    refine ⟨7369953625730879295260179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9826604834307839060346905 7369953625730879295260179)
    ·
      refine ⟨11054930438596318942890269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369953625730879295260179 11054930438596318942890269)
      ·
        refine ⟨4145598914473619603583851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11054930438596318942890269 4145598914473619603583851)
        ·
          refine ⟨6218398371710429405375777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145598914473619603583851 6218398371710429405375777)
          ·
            refine ⟨4663798778782822054031833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6218398371710429405375777 4663798778782822054031833)
            ·
              refine ⟨3497849084087116540523875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663798778782822054031833 3497849084087116540523875)
              ·
                refine ⟨5246773626130674810785813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497849084087116540523875 5246773626130674810785813)
                ·
                  refine ⟨245942513724875381755585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5246773626130674810785813 245942513724875381755585)
                  ·
                    rfl

theorem cell23_4310742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_4310742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310742 prefixEnd_4310742 := by exact prefixLift 4310742
  have htrace : WordTrace (prefixWord ++ tailWord_4310742) baseStart_4310742 baseEnd_4310742 := by
    simpa [prefixWord, tailWord_4310742, baseEnd_4310742] using wordTrace_append hprefix tailTrace_4310742
  have hstable : (prefixWord ++ tailWord_4310742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310742).length < 2 ^ (prefixWord ++ tailWord_4310742).sum := by decide
  have hdescent : baseEnd_4310742 < baseStart_4310742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310744 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_4310744 : Nat := 118140960795 + 4310744 * 2 ^ 59
def prefixEnd_4310744 : Nat := 4983230072969 + 3 ^ 40 * 4310744 * 2
def baseEnd_4310744 : Nat := 2213483650485187427975255

theorem tailTrace_4310744 : CollatzResearch.WordTrace tailWord_4310744 prefixEnd_4310744 2213483650485187427975255 := by
  unfold tailWord_4310744
  simp only [CollatzResearch.WordTrace]
  refine ⟨78612875147459089653561643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104817166863278786204748857 78612875147459089653561643)
  ·
    refine ⟨117919312721188634480342465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78612875147459089653561643 117919312721188634480342465)
    ·
      refine ⟨88439484540891475860256849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117919312721188634480342465 88439484540891475860256849)
      ·
        refine ⟨66329613405668606895192637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88439484540891475860256849 66329613405668606895192637)
        ·
          refine ⟨24873605027125727585697239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66329613405668606895192637 24873605027125727585697239)
          ·
            refine ⟨37310407540688591378545859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24873605027125727585697239 37310407540688591378545859)
            ·
              refine ⟨55965611311032887067818789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37310407540688591378545859 55965611311032887067818789)
              ·
                refine ⟨10493552120818666325216023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55965611311032887067818789 10493552120818666325216023)
                ·
                  refine ⟨15740328181227999487824035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10493552120818666325216023 15740328181227999487824035)
                  ·
                    refine ⟨23610492271841999231736053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15740328181227999487824035 23610492271841999231736053)
                    ·
                      refine ⟨2213483650485187427975255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23610492271841999231736053 2213483650485187427975255)
                      ·
                        rfl

theorem cell23_4310744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_4310744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310744 prefixEnd_4310744 := by exact prefixLift 4310744
  have htrace : WordTrace (prefixWord ++ tailWord_4310744) baseStart_4310744 baseEnd_4310744 := by
    simpa [prefixWord, tailWord_4310744, baseEnd_4310744] using wordTrace_append hprefix tailTrace_4310744
  have hstable : (prefixWord ++ tailWord_4310744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310744).length < 2 ^ (prefixWord ++ tailWord_4310744).sum := by decide
  have hdescent : baseEnd_4310744 < baseStart_4310744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310751 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 2, 4]
def baseStart_4310751 : Nat := 118140960795 + 4310751 * 2 ^ 59
def prefixEnd_4310751 : Nat := 4983230072969 + 3 ^ 40 * 4310751 * 2
def baseEnd_4310751 : Nat := 737829081616589633529241

theorem tailTrace_4310751 : CollatzResearch.WordTrace tailWord_4310751 prefixEnd_4310751 737829081616589633529241 := by
  unfold tailWord_4310751
  simp only [CollatzResearch.WordTrace]
  refine ⟨157226005605892819502628107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104817337070595213001752071 157226005605892819502628107)
  ·
    refine ⟨235839008408839229253942161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157226005605892819502628107 235839008408839229253942161)
    ·
      refine ⟨176879256306629421940456621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235839008408839229253942161 176879256306629421940456621)
      ·
        refine ⟨66329721114986033227671233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176879256306629421940456621 66329721114986033227671233)
        ·
          refine ⟨49747290836239524920753425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66329721114986033227671233 49747290836239524920753425)
          ·
            refine ⟨37310468127179643690565069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49747290836239524920753425 37310468127179643690565069)
            ·
              refine ⟨13991425547692366383961901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37310468127179643690565069 13991425547692366383961901)
              ·
                refine ⟨5246784580384637393985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13991425547692366383961901 5246784580384637393985713)
                ·
                  refine ⟨3935088435288478045489285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5246784580384637393985713 3935088435288478045489285)
                  ·
                    refine ⟨737829081616589633529241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935088435288478045489285 737829081616589633529241)
                    ·
                      rfl

theorem cell23_4310751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_4310751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310751 prefixEnd_4310751 := by exact prefixLift 4310751
  have htrace : WordTrace (prefixWord ++ tailWord_4310751) baseStart_4310751 baseEnd_4310751 := by
    simpa [prefixWord, tailWord_4310751, baseEnd_4310751] using wordTrace_append hprefix tailTrace_4310751
  have hstable : (prefixWord ++ tailWord_4310751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310751).length < 2 ^ (prefixWord ++ tailWord_4310751).sum := by decide
  have hdescent : baseEnd_4310751 < baseStart_4310751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310755 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 1, 5]
def baseStart_4310755 : Nat := 118140960795 + 4310755 * 2 ^ 59
def prefixEnd_4310755 : Nat := 4983230072969 + 3 ^ 40 * 4310755 * 2
def baseEnd_4310755 : Nat := 737829766257462294979235

theorem tailTrace_4310755 : CollatzResearch.WordTrace tailWord_4310755 prefixEnd_4310755 737829766257462294979235 := by
  unfold tailWord_4310755
  simp only [CollatzResearch.WordTrace]
  refine ⟨157226151497878328185773719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104817434331918885457182479 157226151497878328185773719)
  ·
    refine ⟨235839227246817492278660579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157226151497878328185773719 235839227246817492278660579)
    ·
      refine ⟨353758840870226238417990869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235839227246817492278660579 353758840870226238417990869)
      ·
        refine ⟨8291222832895927462921661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 353758840870226238417990869 8291222832895927462921661)
        ·
          refine ⟨3109208562335972798595623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8291222832895927462921661 3109208562335972798595623)
          ·
            refine ⟨4663812843503959197893435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109208562335972798595623 4663812843503959197893435)
            ·
              refine ⟨6995719265255938796840153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663812843503959197893435 6995719265255938796840153)
              ·
                refine ⟨5246789448941954097630115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6995719265255938796840153 5246789448941954097630115)
                ·
                  refine ⟨7870184173412931146445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246789448941954097630115 7870184173412931146445173)
                  ·
                    refine ⟨737829766257462294979235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7870184173412931146445173 737829766257462294979235)
                    ·
                      rfl

theorem cell23_4310755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 5].length) (baseStart_4310755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310755 prefixEnd_4310755 := by exact prefixLift 4310755
  have htrace : WordTrace (prefixWord ++ tailWord_4310755) baseStart_4310755 baseEnd_4310755 := by
    simpa [prefixWord, tailWord_4310755, baseEnd_4310755] using wordTrace_append hprefix tailTrace_4310755
  have hstable : (prefixWord ++ tailWord_4310755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310755).length < 2 ^ (prefixWord ++ tailWord_4310755).sum := by decide
  have hdescent : baseEnd_4310755 < baseStart_4310755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310772 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4310772 : Nat := 118140960795 + 4310772 * 2 ^ 59
def prefixEnd_4310772 : Nat := 4983230072969 + 3 ^ 40 * 4310772 * 2
def baseEnd_4310772 : Nat := 737832675981171106141709

theorem tailTrace_4310772 : CollatzResearch.WordTrace tailWord_4310772 prefixEnd_4310772 737832675981171106141709 := by
  unfold tailWord_4310772
  simp only [CollatzResearch.WordTrace]
  refine ⟨78613385769408370044571285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104817847692544493392761713 78613385769408370044571285)
  ·
    refine ⟨3685002457941017345839279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78613385769408370044571285 3685002457941017345839279)
    ·
      refine ⟨5527503686911526018758919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3685002457941017345839279 5527503686911526018758919)
      ·
        refine ⟨8291255530367289028138379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5527503686911526018758919 8291255530367289028138379)
        ·
          refine ⟨12436883295550933542207569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8291255530367289028138379 12436883295550933542207569)
          ·
            refine ⟨9327662471663200156655677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12436883295550933542207569 9327662471663200156655677)
            ·
              refine ⟨3497873426873700058745879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9327662471663200156655677 3497873426873700058745879)
              ·
                refine ⟨5246810140310550088118819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497873426873700058745879 5246810140310550088118819)
                ·
                  refine ⟨7870215210465825132178229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246810140310550088118819 7870215210465825132178229)
                  ·
                    refine ⟨737832675981171106141709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7870215210465825132178229 737832675981171106141709)
                    ·
                      rfl

theorem cell23_4310772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4310772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310772 prefixEnd_4310772 := by exact prefixLift 4310772
  have htrace : WordTrace (prefixWord ++ tailWord_4310772) baseStart_4310772 baseEnd_4310772 := by
    simpa [prefixWord, tailWord_4310772, baseEnd_4310772] using wordTrace_append hprefix tailTrace_4310772
  have hstable : (prefixWord ++ tailWord_4310772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310772).length < 2 ^ (prefixWord ++ tailWord_4310772).sum := by decide
  have hdescent : baseEnd_4310772 < baseStart_4310772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310794 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_4310794 : Nat := 118140960795 + 4310794 * 2 ^ 59
def prefixEnd_4310794 : Nat := 4983230072969 + 3 ^ 40 * 4310794 * 2
def baseEnd_4310794 : Nat := 737836441505970744116675

theorem tailTrace_4310794 : CollatzResearch.WordTrace tailWord_4310794 prefixEnd_4310794 737836441505970744116675 := by
  unfold tailWord_4310794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39306893486184259461610859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104818382629824691897628957 39306893486184259461610859)
  ·
    refine ⟨58960340229276389192416289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39306893486184259461610859 58960340229276389192416289)
    ·
      refine ⟨44220255171957291894312217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58960340229276389192416289 44220255171957291894312217)
      ·
        refine ⟨33165191378967968920734163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44220255171957291894312217 33165191378967968920734163)
        ·
          refine ⟨49747787068451953381101245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33165191378967968920734163 49747787068451953381101245)
          ·
            refine ⟨18655420150669482517912967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49747787068451953381101245 18655420150669482517912967)
            ·
              refine ⟨27983130226004223776869451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18655420150669482517912967 27983130226004223776869451)
              ·
                refine ⟨41974695339006335665304177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27983130226004223776869451 41974695339006335665304177)
                ·
                  refine ⟨31481021504254751748978133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41974695339006335665304177 31481021504254751748978133)
                  ·
                    refine ⟨737836441505970744116675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31481021504254751748978133 737836441505970744116675)
                    ·
                      rfl

theorem cell23_4310794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_4310794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310794 prefixEnd_4310794 := by exact prefixLift 4310794
  have htrace : WordTrace (prefixWord ++ tailWord_4310794) baseStart_4310794 baseEnd_4310794 := by
    simpa [prefixWord, tailWord_4310794, baseEnd_4310794] using wordTrace_append hprefix tailTrace_4310794
  have hstable : (prefixWord ++ tailWord_4310794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310794).length < 2 ^ (prefixWord ++ tailWord_4310794).sum := by decide
  have hdescent : baseEnd_4310794 < baseStart_4310794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310808 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_4310808 : Nat := 118140960795 + 4310808 * 2 ^ 59
def prefixEnd_4310808 : Nat := 4983230072969 + 3 ^ 40 * 4310808 * 2
def baseEnd_4310808 : Nat := 2213516513247075177574961

theorem tailTrace_4310808 : CollatzResearch.WordTrace tailWord_4310808 prefixEnd_4310808 2213516513247075177574961 := by
  unfold tailWord_4310808
  simp only [CollatzResearch.WordTrace]
  refine ⟨78614042283343159118726539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104818723044457545491635385 78614042283343159118726539)
  ·
    refine ⟨117921063425014738678089809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78614042283343159118726539 117921063425014738678089809)
    ·
      refine ⟨88440797568761054008567357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117921063425014738678089809 88440797568761054008567357)
      ·
        refine ⟨33165299088285395253212759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88440797568761054008567357 33165299088285395253212759)
        ·
          refine ⟨49747948632428092879819139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33165299088285395253212759 49747948632428092879819139)
          ·
            refine ⟨74621922948642139319728709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49747948632428092879819139 74621922948642139319728709)
            ·
              refine ⟨13991610552870401122449133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74621922948642139319728709 13991610552870401122449133)
              ·
                refine ⟨5246853957326400420918425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13991610552870401122449133 5246853957326400420918425)
                ·
                  refine ⟨3935140467994800315688819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5246853957326400420918425 3935140467994800315688819)
                  ·
                    refine ⟨5902710701992200473533229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935140467994800315688819 5902710701992200473533229)
                    ·
                      refine ⟨2213516513247075177574961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5902710701992200473533229 2213516513247075177574961)
                      ·
                        rfl

theorem cell23_4310808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_4310808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310808 prefixEnd_4310808 := by exact prefixLift 4310808
  have htrace : WordTrace (prefixWord ++ tailWord_4310808) baseStart_4310808 baseEnd_4310808 := by
    simpa [prefixWord, tailWord_4310808, baseEnd_4310808] using wordTrace_append hprefix tailTrace_4310808
  have hstable : (prefixWord ++ tailWord_4310808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310808).length < 2 ^ (prefixWord ++ tailWord_4310808).sum := by decide
  have hdescent : baseEnd_4310808 < baseStart_4310808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310818 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_4310818 : Nat := 118140960795 + 4310818 * 2 ^ 59
def prefixEnd_4310818 : Nat := 4983230072969 + 3 ^ 40 * 4310818 * 2
def baseEnd_4310818 : Nat := 2213521648053620138449915

theorem tailTrace_4310818 : CollatzResearch.WordTrace tailWord_4310818 prefixEnd_4310818 2213521648053620138449915 := by
  unfold tailWord_4310818
  simp only [CollatzResearch.WordTrace]
  refine ⟨39307112324162522486329277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104818966197766726630211405 39307112324162522486329277)
  ·
    refine ⟨14740167121560945932373479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39307112324162522486329277 14740167121560945932373479)
    ·
      refine ⟨22110250682341418898560219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14740167121560945932373479 22110250682341418898560219)
      ·
        refine ⟨33165376023512128347840329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22110250682341418898560219 33165376023512128347840329)
        ·
          refine ⟨24874032017634096260880247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33165376023512128347840329 24874032017634096260880247)
          ·
            refine ⟨37311048026451144391320371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24874032017634096260880247 37311048026451144391320371)
            ·
              refine ⟨55966572039676716586980557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37311048026451144391320371 55966572039676716586980557)
              ·
                refine ⟨20987464514878768720117709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55966572039676716586980557 20987464514878768720117709)
                ·
                  refine ⟨7870299193079538270044141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20987464514878768720117709 7870299193079538270044141)
                  ·
                    refine ⟨2951362197404826851266553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7870299193079538270044141 2951362197404826851266553)
                    ·
                      refine ⟨2213521648053620138449915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951362197404826851266553 2213521648053620138449915)
                      ·
                        rfl

theorem cell23_4310818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_4310818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310818 prefixEnd_4310818 := by exact prefixLift 4310818
  have htrace : WordTrace (prefixWord ++ tailWord_4310818) baseStart_4310818 baseEnd_4310818 := by
    simpa [prefixWord, tailWord_4310818, baseEnd_4310818] using wordTrace_append hprefix tailTrace_4310818
  have hstable : (prefixWord ++ tailWord_4310818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310818).length < 2 ^ (prefixWord ++ tailWord_4310818).sum := by decide
  have hdescent : baseEnd_4310818 < baseStart_4310818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310835 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 1, 3, 2]
def baseStart_4310835 : Nat := 118140960795 + 4310835 * 2 ^ 59
def prefixEnd_4310835 : Nat := 4983230072969 + 3 ^ 40 * 4310835 * 2
def baseEnd_4310835 : Nat := 2213530377224746571937337

theorem tailTrace_4310835 : CollatzResearch.WordTrace tailWord_4310835 prefixEnd_4310835 2213530377224746571937337 := by
  unfold tailWord_4310835
  simp only [CollatzResearch.WordTrace]
  refine ⟨157229069337588501848685959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104819379558392334565790639 157229069337588501848685959)
  ·
    refine ⟨235843604006382752773028939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157229069337588501848685959 235843604006382752773028939)
    ·
      refine ⟨353765406009574129159543409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235843604006382752773028939 353765406009574129159543409)
      ·
        refine ⟨265324054507180596869657557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353765406009574129159543409 265324054507180596869657557)
        ·
          refine ⟨6218532527512045239132599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 265324054507180596869657557 6218532527512045239132599)
          ·
            refine ⟨9327798791268067858698899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218532527512045239132599 9327798791268067858698899)
            ·
              refine ⟨13991698186902101788048349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9327798791268067858698899 13991698186902101788048349)
              ·
                refine ⟨5246886820088288170518131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13991698186902101788048349 5246886820088288170518131)
                ·
                  refine ⟨7870330230132432255777197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246886820088288170518131 7870330230132432255777197)
                  ·
                    refine ⟨2951373836299662095916449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7870330230132432255777197 2951373836299662095916449)
                    ·
                      refine ⟨2213530377224746571937337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951373836299662095916449 2213530377224746571937337)
                      ·
                        rfl

theorem cell23_4310835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3, 2].length) (baseStart_4310835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310835 prefixEnd_4310835 := by exact prefixLift 4310835
  have htrace : WordTrace (prefixWord ++ tailWord_4310835) baseStart_4310835 baseEnd_4310835 := by
    simpa [prefixWord, tailWord_4310835, baseEnd_4310835] using wordTrace_append hprefix tailTrace_4310835
  have hstable : (prefixWord ++ tailWord_4310835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310835).length < 2 ^ (prefixWord ++ tailWord_4310835).sum := by decide
  have hdescent : baseEnd_4310835 < baseStart_4310835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310865 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_4310865 : Nat := 118140960795 + 4310865 * 2 ^ 59
def prefixEnd_4310865 : Nat := 4983230072969 + 3 ^ 40 * 4310865 * 2
def baseEnd_4310865 : Nat := 2213545781644381454562199

theorem tailTrace_4310865 : CollatzResearch.WordTrace tailWord_4310865 prefixEnd_4310865 2213545781644381454562199 := by
  unfold tailWord_4310865
  simp only [CollatzResearch.WordTrace]
  refine ⟨157230163527479816972278049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104820109018319877981518699 157230163527479816972278049)
  ·
    refine ⟨117922622645609862729208537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157230163527479816972278049 117922622645609862729208537)
    ·
      refine ⟨88441966984207397046906403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117922622645609862729208537 88441966984207397046906403)
      ·
        refine ⟨132662950476311095570359605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88441966984207397046906403 132662950476311095570359605)
        ·
          refine ⟨12437151607154165209721213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132662950476311095570359605 12437151607154165209721213)
          ·
            refine ⟨4663931852682811953645455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12437151607154165209721213 4663931852682811953645455)
            ·
              refine ⟨6995897779024217930468183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663931852682811953645455 6995897779024217930468183)
              ·
                refine ⟨10493846668536326895702275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6995897779024217930468183 10493846668536326895702275)
                ·
                  refine ⟨15740770002804490343553413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10493846668536326895702275 15740770002804490343553413)
                  ·
                    refine ⟨2951394375525841939416265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15740770002804490343553413 2951394375525841939416265)
                    ·
                      refine ⟨2213545781644381454562199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951394375525841939416265 2213545781644381454562199)
                      ·
                        rfl

theorem cell23_4310865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_4310865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310865 prefixEnd_4310865 := by exact prefixLift 4310865
  have htrace : WordTrace (prefixWord ++ tailWord_4310865) baseStart_4310865 baseEnd_4310865 := by
    simpa [prefixWord, tailWord_4310865, baseEnd_4310865] using wordTrace_append hprefix tailTrace_4310865
  have hstable : (prefixWord ++ tailWord_4310865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310865).length < 2 ^ (prefixWord ++ tailWord_4310865).sum := by decide
  have hdescent : baseEnd_4310865 < baseStart_4310865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310891 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 7, 2]
def baseStart_4310891 : Nat := 118140960795 + 4310891 * 2 ^ 59
def prefixEnd_4310891 : Nat := 4983230072969 + 3 ^ 40 * 4310891 * 2
def baseEnd_4310891 : Nat := 2213559132141398352837079

theorem tailTrace_4310891 : CollatzResearch.WordTrace tailWord_4310891 prefixEnd_4310891 2213559132141398352837079 := by
  unfold tailWord_4310891
  simp only [CollatzResearch.WordTrace]
  refine ⟨157231111825385623412724527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104820741216923748941816351 157231111825385623412724527)
  ·
    refine ⟨235846667738078435119086791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157231111825385623412724527 235846667738078435119086791)
    ·
      refine ⟨353770001607117652678630187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235846667738078435119086791 353770001607117652678630187)
      ·
        refine ⟨530655002410676479017945281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353770001607117652678630187 530655002410676479017945281)
        ·
          refine ⟨397991251808007359263458961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530655002410676479017945281 397991251808007359263458961)
          ·
            refine ⟨298493438856005519447594221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397991251808007359263458961 298493438856005519447594221)
            ·
              refine ⟨111935039571002069792847833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 298493438856005519447594221 111935039571002069792847833)
              ·
                refine ⟨83951279678251552344635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111935039571002069792847833 83951279678251552344635875)
                ·
                  refine ⟨125926919517377328516953813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83951279678251552344635875 125926919517377328516953813)
                  ·
                    refine ⟨2951412176188531137116105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125926919517377328516953813 2951412176188531137116105)
                    ·
                      refine ⟨2213559132141398352837079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951412176188531137116105 2213559132141398352837079)
                      ·
                        rfl

theorem cell23_4310891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7, 2].length) (baseStart_4310891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310891 prefixEnd_4310891 := by exact prefixLift 4310891
  have htrace : WordTrace (prefixWord ++ tailWord_4310891) baseStart_4310891 baseEnd_4310891 := by
    simpa [prefixWord, tailWord_4310891, baseEnd_4310891] using wordTrace_append hprefix tailTrace_4310891
  have hstable : (prefixWord ++ tailWord_4310891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310891).length < 2 ^ (prefixWord ++ tailWord_4310891).sum := by decide
  have hdescent : baseEnd_4310891 < baseStart_4310891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310921 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_4310921 : Nat := 118140960795 + 4310921 * 2 ^ 59
def prefixEnd_4310921 : Nat := 4983230072969 + 3 ^ 40 * 4310921 * 2
def baseEnd_4310921 : Nat := 2213574536561033235461941

theorem tailTrace_4310921 : CollatzResearch.WordTrace tailWord_4310921 prefixEnd_4310921 2213574536561033235461941 := by
  unfold tailWord_4310921
  simp only [CollatzResearch.WordTrace]
  refine ⟨157232206015276938536316617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104821470676851292357544411 157232206015276938536316617)
  ·
    refine ⟨117924154511457703902237463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157232206015276938536316617 117924154511457703902237463)
    ·
      refine ⟨176886231767186555853356195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117924154511457703902237463 176886231767186555853356195)
      ·
        refine ⟨265329347650779833780034293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176886231767186555853356195 265329347650779833780034293)
        ·
          refine ⟨24874626342260609416878215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265329347650779833780034293 24874626342260609416878215)
          ·
            refine ⟨37311939513390914125317323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24874626342260609416878215 37311939513390914125317323)
            ·
              refine ⟨55967909270086371187975985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37311939513390914125317323 55967909270086371187975985)
              ·
                refine ⟨41975931952564778390981989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55967909270086371187975985 41975931952564778390981989)
                ·
                  refine ⟨7870487241105895948309123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41975931952564778390981989 7870487241105895948309123)
                  ·
                    refine ⟨11805730861658843922463685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7870487241105895948309123 11805730861658843922463685)
                    ·
                      refine ⟨2213574536561033235461941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11805730861658843922463685 2213574536561033235461941)
                      ·
                        rfl

theorem cell23_4310921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_4310921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310921 prefixEnd_4310921 := by exact prefixLift 4310921
  have htrace : WordTrace (prefixWord ++ tailWord_4310921) baseStart_4310921 baseEnd_4310921 := by
    simpa [prefixWord, tailWord_4310921, baseEnd_4310921] using wordTrace_append hprefix tailTrace_4310921
  have hstable : (prefixWord ++ tailWord_4310921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310921).length < 2 ^ (prefixWord ++ tailWord_4310921).sum := by decide
  have hdescent : baseEnd_4310921 < baseStart_4310921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310938 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4310938 : Nat := 118140960795 + 4310938 * 2 ^ 59
def prefixEnd_4310938 : Nat := 4983230072969 + 3 ^ 40 * 4310938 * 2
def baseEnd_4310938 : Nat := 2213583265732159668949363

theorem tailTrace_4310938 : CollatzResearch.WordTrace tailWord_4310938 prefixEnd_4310938 2213583265732159668949363 := by
  unfold tailWord_4310938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39308206514053837609921367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104821884037476900293123645 39308206514053837609921367)
  ·
    refine ⟨58962309771080756414882051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39308206514053837609921367 58962309771080756414882051)
    ·
      refine ⟨88443464656621134622323077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58962309771080756414882051 88443464656621134622323077)
      ·
        refine ⟨16583149623116462741685577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88443464656621134622323077 16583149623116462741685577)
        ·
          refine ⟨12437362217337347056264183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16583149623116462741685577 12437362217337347056264183)
          ·
            refine ⟨18656043326006020584396275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12437362217337347056264183 18656043326006020584396275)
            ·
              refine ⟨27984064989009030876594413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18656043326006020584396275 27984064989009030876594413)
              ·
                refine ⟨10494024370878386578722905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27984064989009030876594413 10494024370878386578722905)
                ·
                  refine ⟨7870518278158789934042179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10494024370878386578722905 7870518278158789934042179)
                  ·
                    refine ⟨11805777417238184901063269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7870518278158789934042179 11805777417238184901063269)
                    ·
                      refine ⟨2213583265732159668949363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11805777417238184901063269 2213583265732159668949363)
                      ·
                        rfl

theorem cell23_4310938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4310938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310938 prefixEnd_4310938 := by exact prefixLift 4310938
  have htrace : WordTrace (prefixWord ++ tailWord_4310938) baseStart_4310938 baseEnd_4310938 := by
    simpa [prefixWord, tailWord_4310938, baseEnd_4310938] using wordTrace_append hprefix tailTrace_4310938
  have hstable : (prefixWord ++ tailWord_4310938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310938).length < 2 ^ (prefixWord ++ tailWord_4310938).sum := by decide
  have hdescent : baseEnd_4310938 < baseStart_4310938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310972 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4310972 : Nat := 118140960795 + 4310972 * 2 ^ 59
def prefixEnd_4310972 : Nat := 4983230072969 + 3 ^ 40 * 4310972 * 2
def baseEnd_4310972 : Nat := 2213600724074412535924207

theorem tailTrace_4310972 : CollatzResearch.WordTrace tailWord_4310972 prefixEnd_4310972 2213600724074412535924207 := by
  unfold tailWord_4310972
  simp only [CollatzResearch.WordTrace]
  refine ⟨78617033069046087123211585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104822710758728116164282113 78617033069046087123211585)
  ·
    refine ⟨58962774801784565342408689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78617033069046087123211585 58962774801784565342408689)
    ·
      refine ⟨44222081101338424006806517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58962774801784565342408689 44222081101338424006806517)
      ·
        refine ⟨4145820103250477250638111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44222081101338424006806517 4145820103250477250638111)
        ·
          refine ⟨6218730154875715875957167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145820103250477250638111 6218730154875715875957167)
          ·
            refine ⟨9328095232313573813935751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218730154875715875957167 9328095232313573813935751)
            ·
              refine ⟨13992142848470360720903627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9328095232313573813935751 13992142848470360720903627)
              ·
                refine ⟨20988214272705541081355441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13992142848470360720903627 20988214272705541081355441)
                ·
                  refine ⟨15741160704529155811016581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20988214272705541081355441 15741160704529155811016581)
                  ·
                    refine ⟨2951467632099216714565609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15741160704529155811016581 2951467632099216714565609)
                    ·
                      refine ⟨2213600724074412535924207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951467632099216714565609 2213600724074412535924207)
                      ·
                        rfl

theorem cell23_4310972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4310972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310972 prefixEnd_4310972 := by exact prefixLift 4310972
  have htrace : WordTrace (prefixWord ++ tailWord_4310972) baseStart_4310972 baseEnd_4310972 := by
    simpa [prefixWord, tailWord_4310972, baseEnd_4310972] using wordTrace_append hprefix tailTrace_4310972
  have hstable : (prefixWord ++ tailWord_4310972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310972).length < 2 ^ (prefixWord ++ tailWord_4310972).sum := by decide
  have hdescent : baseEnd_4310972 < baseStart_4310972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4310991 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 3, 5]
def baseStart_4310991 : Nat := 118140960795 + 4310991 * 2 ^ 59
def prefixEnd_4310991 : Nat := 4983230072969 + 3 ^ 40 * 4310991 * 2
def baseEnd_4310991 : Nat := 737870160068949320528873

theorem tailTrace_4310991 : CollatzResearch.WordTrace tailWord_4310991 prefixEnd_4310991 737870160068949320528873 := by
  unfold tailWord_4310991
  simp only [CollatzResearch.WordTrace]
  refine ⟨157234759125023340491364827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104823172750015560327576551 157234759125023340491364827)
  ·
    refine ⟨235852138687535010737047241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157234759125023340491364827 235852138687535010737047241)
    ·
      refine ⟨176889104015651258052785431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235852138687535010737047241 176889104015651258052785431)
      ·
        refine ⟨265333656023476887079178147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176889104015651258052785431 265333656023476887079178147)
        ·
          refine ⟨398000484035215330618767221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265333656023476887079178147 398000484035215330618767221)
          ·
            refine ⟨37312545378301437245509427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 398000484035215330618767221 37312545378301437245509427)
            ·
              refine ⟨55968818067452155868264141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37312545378301437245509427 55968818067452155868264141)
              ·
                refine ⟨20988306775294558450599053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55968818067452155868264141 20988306775294558450599053)
                ·
                  refine ⟨7870615040735459418974645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20988306775294558450599053 7870615040735459418974645)
                  ·
                    refine ⟨737870160068949320528873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7870615040735459418974645 737870160068949320528873)
                    ·
                      rfl

theorem cell23_4310991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_4310991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4310991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4310991 prefixEnd_4310991 := by exact prefixLift 4310991
  have htrace : WordTrace (prefixWord ++ tailWord_4310991) baseStart_4310991 baseEnd_4310991 := by
    simpa [prefixWord, tailWord_4310991, baseEnd_4310991] using wordTrace_append hprefix tailTrace_4310991
  have hstable : (prefixWord ++ tailWord_4310991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4310991).length < 2 ^ (prefixWord ++ tailWord_4310991).sum := by decide
  have hdescent : baseEnd_4310991 < baseStart_4310991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4310991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311022 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_4311022 : Nat := 118140960795 + 4311022 * 2 ^ 59
def prefixEnd_4311022 : Nat := 4983230072969 + 3 ^ 40 * 4311022 * 2
def baseEnd_4311022 : Nat := 2213626398107137340298977

theorem tailTrace_4311022 : CollatzResearch.WordTrace tailWord_4311022 prefixEnd_4311022 2213626398107137340298977 := by
  unfold tailWord_4311022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19654486223488879098217915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104823926525274021857162213 19654486223488879098217915)
  ·
    refine ⟨29481729335233318647326873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19654486223488879098217915 29481729335233318647326873)
    ·
      refine ⟨22111297001424988985495155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29481729335233318647326873 22111297001424988985495155)
      ·
        refine ⟨33166945502137483478242733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22111297001424988985495155 33166945502137483478242733)
        ·
          refine ⟨12437604563301556304341025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33166945502137483478242733 12437604563301556304341025)
          ·
            refine ⟨9328203422476167228255769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12437604563301556304341025 9328203422476167228255769)
            ·
              refine ⟨6996152566857125421191827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9328203422476167228255769 6996152566857125421191827)
              ·
                refine ⟨10494228850285688131787741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6996152566857125421191827 10494228850285688131787741)
                ·
                  refine ⟨3935335818857133049420403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10494228850285688131787741 3935335818857133049420403)
                  ·
                    refine ⟨5903003728285699574130605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935335818857133049420403 5903003728285699574130605)
                    ·
                      refine ⟨2213626398107137340298977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903003728285699574130605 2213626398107137340298977)
                      ·
                        rfl

theorem cell23_4311022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_4311022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311022 prefixEnd_4311022 := by exact prefixLift 4311022
  have htrace : WordTrace (prefixWord ++ tailWord_4311022) baseStart_4311022 baseEnd_4311022 := by
    simpa [prefixWord, tailWord_4311022, baseEnd_4311022] using wordTrace_append hprefix tailTrace_4311022
  have hstable : (prefixWord ++ tailWord_4311022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311022).length < 2 ^ (prefixWord ++ tailWord_4311022).sum := by decide
  have hdescent : baseEnd_4311022 < baseStart_4311022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311045 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_4311045 : Nat := 118140960795 + 4311045 * 2 ^ 59
def prefixEnd_4311045 : Nat := 4983230072969 + 3 ^ 40 * 4311045 * 2
def baseEnd_4311045 : Nat := 2213638208162190750311371

theorem tailTrace_4311045 : CollatzResearch.WordTrace tailWord_4311045 prefixEnd_4311045 2213638208162190750311371 := by
  unfold tailWord_4311045
  simp only [CollatzResearch.WordTrace]
  refine ⟨157236728666827707713830589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104824485777885138475887059 157236728666827707713830589)
  ·
    refine ⟨58963773250060390392686471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157236728666827707713830589 58963773250060390392686471)
    ·
      refine ⟨88445659875090585589029707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58963773250060390392686471 88445659875090585589029707)
      ·
        refine ⟨132668489812635878383544561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88445659875090585589029707 132668489812635878383544561)
        ·
          refine ⟨99501367359476908787658421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132668489812635878383544561 99501367359476908787658421)
          ·
            refine ⟨9328253189950960198842977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99501367359476908787658421 9328253189950960198842977)
            ·
              refine ⟨6996189892463220149132233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9328253189950960198842977 6996189892463220149132233)
              ·
                refine ⟨5247142419347415111849175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6996189892463220149132233 5247142419347415111849175)
                ·
                  refine ⟨7870713629021122667773763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5247142419347415111849175 7870713629021122667773763)
                  ·
                    refine ⟨11806070443531684001660645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7870713629021122667773763 11806070443531684001660645)
                    ·
                      refine ⟨2213638208162190750311371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11806070443531684001660645 2213638208162190750311371)
                      ·
                        rfl

theorem cell23_4311045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_4311045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311045 prefixEnd_4311045 := by exact prefixLift 4311045
  have htrace : WordTrace (prefixWord ++ tailWord_4311045) baseStart_4311045 baseEnd_4311045 := by
    simpa [prefixWord, tailWord_4311045, baseEnd_4311045] using wordTrace_append hprefix tailTrace_4311045
  have hstable : (prefixWord ++ tailWord_4311045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311045).length < 2 ^ (prefixWord ++ tailWord_4311045).sum := by decide
  have hdescent : baseEnd_4311045 < baseStart_4311045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311051 : List Nat := [1, 1, 1, 1, 6, 1, 3, 9]
def baseStart_4311051 : Nat := 118140960795 + 4311051 * 2 ^ 59
def prefixEnd_4311051 : Nat := 4983230072969 + 3 ^ 40 * 4311051 * 2
def baseEnd_4311051 : Nat := 81986714409115471364309

theorem tailTrace_4311051 : CollatzResearch.WordTrace tailWord_4311051 prefixEnd_4311051 81986714409115471364309 := by
  unfold tailWord_4311051
  simp only [CollatzResearch.WordTrace]
  refine ⟨157236947504805970738549007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104824631669870647159032671 157236947504805970738549007)
  ·
    refine ⟨235855421257208956107823511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157236947504805970738549007 235855421257208956107823511)
    ·
      refine ⟨353783131885813434161735267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235855421257208956107823511 353783131885813434161735267)
      ·
        refine ⟨530674697828720151242602901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353783131885813434161735267 530674697828720151242602901)
        ·
          refine ⟨24875376460721257089497011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 530674697828720151242602901 24875376460721257089497011)
          ·
            refine ⟨37313064691081885634245517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24875376460721257089497011 37313064691081885634245517)
            ·
              refine ⟨13992399259155707112842069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37313064691081885634245517 13992399259155707112842069)
              ·
                refine ⟨81986714409115471364309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13992399259155707112842069 81986714409115471364309)
                ·
                  rfl

theorem cell23_4311051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 9].length) (baseStart_4311051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311051 prefixEnd_4311051 := by exact prefixLift 4311051
  have htrace : WordTrace (prefixWord ++ tailWord_4311051) baseStart_4311051 baseEnd_4311051 := by
    simpa [prefixWord, tailWord_4311051, baseEnd_4311051] using wordTrace_append hprefix tailTrace_4311051
  have hstable : (prefixWord ++ tailWord_4311051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311051).length < 2 ^ (prefixWord ++ tailWord_4311051).sum := by decide
  have hdescent : baseEnd_4311051 < baseStart_4311051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311068 : List Nat := [2, 2, 3, 1, 3, 3, 9]
def baseStart_4311068 : Nat := 118140960795 + 4311068 * 2 ^ 59
def prefixEnd_4311068 : Nat := 4983230072969 + 3 ^ 40 * 4311068 * 2
def baseEnd_4311068 : Nat := 27329012570583261238565

theorem tailTrace_4311068 : CollatzResearch.WordTrace tailWord_4311068 prefixEnd_4311068 27329012570583261238565 := by
  unfold tailWord_4311068
  simp only [CollatzResearch.WordTrace]
  refine ⟨78618783772872191320958929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104825045030496255094611905 78618783772872191320958929)
  ·
    refine ⟨58964087829654143490719197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78618783772872191320958929 58964087829654143490719197)
    ·
      refine ⟨22111532936120303809019699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58964087829654143490719197 22111532936120303809019699)
      ·
        refine ⟨33167299404180455713529549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22111532936120303809019699 33167299404180455713529549)
        ·
          refine ⟨12437737276567670892573581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33167299404180455713529549 12437737276567670892573581)
          ·
            refine ⟨4664151478712876584715093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12437737276567670892573581 4664151478712876584715093)
            ·
              refine ⟨27329012570583261238565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4664151478712876584715093 27329012570583261238565)
              ·
                rfl

theorem cell23_4311068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 9].length) (baseStart_4311068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311068 prefixEnd_4311068 := by exact prefixLift 4311068
  have htrace : WordTrace (prefixWord ++ tailWord_4311068) baseStart_4311068 baseEnd_4311068 := by
    simpa [prefixWord, tailWord_4311068, baseEnd_4311068] using wordTrace_append hprefix tailTrace_4311068
  have hstable : (prefixWord ++ tailWord_4311068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311068).length < 2 ^ (prefixWord ++ tailWord_4311068).sum := by decide
  have hdescent : baseEnd_4311068 < baseStart_4311068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311148 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_4311148 : Nat := 118140960795 + 4311148 * 2 ^ 59
def prefixEnd_4311148 : Nat := 4983230072969 + 3 ^ 40 * 4311148 * 2
def baseEnd_4311148 : Nat := 2213691096669603847323397

theorem tailTrace_4311148 : CollatzResearch.WordTrace tailWord_4311148 prefixEnd_4311148 2213691096669603847323397 := by
  unfold tailWord_4311148
  simp only [CollatzResearch.WordTrace]
  refine ⟨78620242692727278152415049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104826990256969704203220065 78620242692727278152415049)
  ·
    refine ⟨58965182019545458614311287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78620242692727278152415049 58965182019545458614311287)
    ·
      refine ⟨88447773029318187921466931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58965182019545458614311287 88447773029318187921466931)
      ·
        refine ⟨132671659543977281882200397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88447773029318187921466931 132671659543977281882200397)
        ·
          refine ⟨49751872328991480705825149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132671659543977281882200397 49751872328991480705825149)
          ·
            refine ⟨18656952123371805264684431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49751872328991480705825149 18656952123371805264684431)
            ·
              refine ⟨27985428185057707897026647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18656952123371805264684431 27985428185057707897026647)
              ·
                refine ⟨41978142277586561845539971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27985428185057707897026647 41978142277586561845539971)
                ·
                  refine ⟨62967213416379842768309957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41978142277586561845539971 62967213416379842768309957)
                  ·
                    refine ⟨11806352515571220519058117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62967213416379842768309957 11806352515571220519058117)
                    ·
                      refine ⟨2213691096669603847323397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11806352515571220519058117 2213691096669603847323397)
                      ·
                        rfl

theorem cell23_4311148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_4311148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311148 prefixEnd_4311148 := by exact prefixLift 4311148
  have htrace : WordTrace (prefixWord ++ tailWord_4311148) baseStart_4311148 baseEnd_4311148 := by
    simpa [prefixWord, tailWord_4311148, baseEnd_4311148] using wordTrace_append hprefix tailTrace_4311148
  have hstable : (prefixWord ++ tailWord_4311148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311148).length < 2 ^ (prefixWord ++ tailWord_4311148).sum := by decide
  have hdescent : baseEnd_4311148 < baseStart_4311148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311152 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2]
def baseStart_4311152 : Nat := 118140960795 + 4311152 * 2 ^ 59
def prefixEnd_4311152 : Nat := 4983230072969 + 3 ^ 40 * 4311152 * 2
def baseEnd_4311152 : Nat := 2213693150592221831673379

theorem tailTrace_4311152 : CollatzResearch.WordTrace tailWord_4311152 prefixEnd_4311152 2213693150592221831673379 := by
  unfold tailWord_4311152
  simp only [CollatzResearch.WordTrace]
  refine ⟨78620315638720032493987855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104827087518293376658650473 78620315638720032493987855)
  ·
    refine ⟨117930473458080048740981783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78620315638720032493987855 117930473458080048740981783)
    ·
      refine ⟨176895710187120073111472675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117930473458080048740981783 176895710187120073111472675)
      ·
        refine ⟨265343565280680109667209013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176895710187120073111472675 265343565280680109667209013)
        ·
          refine ⟨24875959245063760281300845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265343565280680109667209013 24875959245063760281300845)
          ·
            refine ⟨9328484716898910105487817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24875959245063760281300845 9328484716898910105487817)
            ·
              refine ⟨6996363537674182579115863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9328484716898910105487817 6996363537674182579115863)
              ·
                refine ⟨10494545306511273868673795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6996363537674182579115863 10494545306511273868673795)
                ·
                  refine ⟨15741817959766910803010693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10494545306511273868673795 15741817959766910803010693)
                  ·
                    refine ⟨2951590867456295775564505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15741817959766910803010693 2951590867456295775564505)
                    ·
                      refine ⟨2213693150592221831673379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951590867456295775564505 2213693150592221831673379)
                      ·
                        rfl

theorem cell23_4311152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2].length) (baseStart_4311152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311152 prefixEnd_4311152 := by exact prefixLift 4311152
  have htrace : WordTrace (prefixWord ++ tailWord_4311152) baseStart_4311152 baseEnd_4311152 := by
    simpa [prefixWord, tailWord_4311152, baseEnd_4311152] using wordTrace_append hprefix tailTrace_4311152
  have hstable : (prefixWord ++ tailWord_4311152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311152).length < 2 ^ (prefixWord ++ tailWord_4311152).sum := by decide
  have hdescent : baseEnd_4311152 < baseStart_4311152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311168 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_4311168 : Nat := 118140960795 + 4311168 * 2 ^ 59
def prefixEnd_4311168 : Nat := 4983230072969 + 3 ^ 40 * 4311168 * 2
def baseEnd_4311168 : Nat := 2213701366282693769073305

theorem tailTrace_4311168 : CollatzResearch.WordTrace tailWord_4311168 prefixEnd_4311168 2213701366282693769073305 := by
  unfold tailWord_4311168
  simp only [CollatzResearch.WordTrace]
  refine ⟨78620607422691049860279079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104827476563588066480372105 78620607422691049860279079)
  ·
    refine ⟨117930911134036574790418619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78620607422691049860279079 117930911134036574790418619)
    ·
      refine ⟨176896366701054862185627929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117930911134036574790418619 176896366701054862185627929)
      ·
        refine ⟨132672275025791146639220947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176896366701054862185627929 132672275025791146639220947)
        ·
          refine ⟨199008412538686719958831421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132672275025791146639220947 199008412538686719958831421)
          ·
            refine ⟨74628154702007519984561783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199008412538686719958831421 74628154702007519984561783)
            ·
              refine ⟨111942232053011279976842675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74628154702007519984561783 111942232053011279976842675)
              ·
                refine ⟨167913348079516919965264013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111942232053011279976842675 167913348079516919965264013)
                ·
                  refine ⟨62967505529818844986974005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167913348079516919965264013 62967505529818844986974005)
                  ·
                    refine ⟨5903203643420516717528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62967505529818844986974005 5903203643420516717528813)
                    ·
                      refine ⟨2213701366282693769073305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903203643420516717528813 2213701366282693769073305)
                      ·
                        rfl

theorem cell23_4311168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_4311168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311168 prefixEnd_4311168 := by exact prefixLift 4311168
  have htrace : WordTrace (prefixWord ++ tailWord_4311168) baseStart_4311168 baseEnd_4311168 := by
    simpa [prefixWord, tailWord_4311168, baseEnd_4311168] using wordTrace_append hprefix tailTrace_4311168
  have hstable : (prefixWord ++ tailWord_4311168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311168).length < 2 ^ (prefixWord ++ tailWord_4311168).sum := by decide
  have hdescent : baseEnd_4311168 < baseStart_4311168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311175 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 5]
def baseStart_4311175 : Nat := 118140960795 + 4311175 * 2 ^ 59
def prefixEnd_4311175 : Nat := 4983230072969 + 3 ^ 40 * 4311175 * 2
def baseEnd_4311175 : Nat := 245967217849697249076197

theorem tailTrace_4311175 : CollatzResearch.WordTrace tailWord_4311175 prefixEnd_4311175 245967217849697249076197 := by
  unfold tailWord_4311175
  simp only [CollatzResearch.WordTrace]
  refine ⟨157241470156356739916062979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104827646770904493277375319 157241470156356739916062979)
  ·
    refine ⟨235862205234535109874094469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157241470156356739916062979 235862205234535109874094469)
    ·
      refine ⟨44224163481475333101392713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235862205234535109874094469 44224163481475333101392713)
      ·
        refine ⟨33168122611106499826044535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44224163481475333101392713 33168122611106499826044535)
        ·
          refine ⟨49752183916659749739066803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33168122611106499826044535 49752183916659749739066803)
          ·
            refine ⟨74628275874989624608600205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49752183916659749739066803 74628275874989624608600205)
            ·
              refine ⟨27985603453121109228225077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74628275874989624608600205 27985603453121109228225077)
              ·
                refine ⟨2623650323730103990146101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27985603453121109228225077 2623650323730103990146101)
                ·
                  refine ⟨245967217849697249076197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623650323730103990146101 245967217849697249076197)
                  ·
                    rfl

theorem cell23_4311175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 5].length) (baseStart_4311175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311175 prefixEnd_4311175 := by exact prefixLift 4311175
  have htrace : WordTrace (prefixWord ++ tailWord_4311175) baseStart_4311175 baseEnd_4311175 := by
    simpa [prefixWord, tailWord_4311175, baseEnd_4311175] using wordTrace_append hprefix tailTrace_4311175
  have hstable : (prefixWord ++ tailWord_4311175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311175).length < 2 ^ (prefixWord ++ tailWord_4311175).sum := by decide
  have hdescent : baseEnd_4311175 < baseStart_4311175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311202 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4311202 : Nat := 118140960795 + 4311202 * 2 ^ 59
def prefixEnd_4311202 : Nat := 4983230072969 + 3 ^ 40 * 4311202 * 2
def baseEnd_4311202 : Nat := 2213718824624946636048149

theorem tailTrace_4311202 : CollatzResearch.WordTrace tailWord_4311202 prefixEnd_4311202 2213718824624946636048149 := by
  unfold tailWord_4311202
  simp only [CollatzResearch.WordTrace]
  refine ⟨39310613731814730881823965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104828303284839282351530573 39310613731814730881823965)
  ·
    refine ⟨14741480149430524080683987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39310613731814730881823965 14741480149430524080683987)
    ·
      refine ⟨22112220224145786121025981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14741480149430524080683987 22112220224145786121025981)
      ·
        refine ⟨8292082584054669795384743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22112220224145786121025981 8292082584054669795384743)
        ·
          refine ⟨12438123876082004693077115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292082584054669795384743 12438123876082004693077115)
          ·
            refine ⟨18657185814123007039615673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12438123876082004693077115 18657185814123007039615673)
            ·
              refine ⟨13992889360592255279711755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18657185814123007039615673 13992889360592255279711755)
              ·
                refine ⟨20989334040888382919567633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13992889360592255279711755 20989334040888382919567633)
                ·
                  refine ⟨15742000530666287189675725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20989334040888382919567633 15742000530666287189675725)
                  ·
                    refine ⟨5903250198999857696128397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15742000530666287189675725 5903250198999857696128397)
                    ·
                      refine ⟨2213718824624946636048149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903250198999857696128397 2213718824624946636048149)
                      ·
                        rfl

theorem cell23_4311202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4311202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311202 prefixEnd_4311202 := by exact prefixLift 4311202
  have htrace : WordTrace (prefixWord ++ tailWord_4311202) baseStart_4311202 baseEnd_4311202 := by
    simpa [prefixWord, tailWord_4311202, baseEnd_4311202] using wordTrace_append hprefix tailTrace_4311202
  have hstable : (prefixWord ++ tailWord_4311202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311202).length < 2 ^ (prefixWord ++ tailWord_4311202).sum := by decide
  have hdescent : baseEnd_4311202 < baseStart_4311202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311218 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_4311218 : Nat := 118140960795 + 4311218 * 2 ^ 59
def prefixEnd_4311218 : Nat := 4983230072969 + 3 ^ 40 * 4311218 * 2
def baseEnd_4311218 : Nat := 737909013438472857816025

theorem tailTrace_4311218 : CollatzResearch.WordTrace tailWord_4311218 prefixEnd_4311218 737909013438472857816025 := by
  unfold tailWord_4311218
  simp only [CollatzResearch.WordTrace]
  refine ⟨39310759623800239564969577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104828692330133972173252205 39310759623800239564969577)
  ·
    refine ⟨29483069717850179673727183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39310759623800239564969577 29483069717850179673727183)
    ·
      refine ⟨44224604576775269510590775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29483069717850179673727183 44224604576775269510590775)
      ·
        refine ⟨66336906865162904265886163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44224604576775269510590775 66336906865162904265886163)
        ·
          refine ⟨99505360297744356398829245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66336906865162904265886163 99505360297744356398829245)
          ·
            refine ⟨37314510111654133649560967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99505360297744356398829245 37314510111654133649560967)
            ·
              refine ⟨55971765167481200474341451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37314510111654133649560967 55971765167481200474341451)
              ·
                refine ⟨83957647751221800711512177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55971765167481200474341451 83957647751221800711512177)
                ·
                  refine ⟨62968235813416350533634133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83957647751221800711512177 62968235813416350533634133)
                  ·
                    refine ⟨737909013438472857816025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62968235813416350533634133 737909013438472857816025)
                    ·
                      rfl

theorem cell23_4311218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_4311218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311218 prefixEnd_4311218 := by exact prefixLift 4311218
  have htrace : WordTrace (prefixWord ++ tailWord_4311218) baseStart_4311218 baseEnd_4311218 := by
    simpa [prefixWord, tailWord_4311218, baseEnd_4311218] using wordTrace_append hprefix tailTrace_4311218
  have hstable : (prefixWord ++ tailWord_4311218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311218).length < 2 ^ (prefixWord ++ tailWord_4311218).sum := by decide
  have hdescent : baseEnd_4311218 < baseStart_4311218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311225 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4311225 : Nat := 118140960795 + 4311225 * 2 ^ 59
def prefixEnd_4311225 : Nat := 4983230072969 + 3 ^ 40 * 4311225 * 2
def baseEnd_4311225 : Nat := 2213730634680000046060543

theorem tailTrace_4311225 : CollatzResearch.WordTrace tailWord_4311225 prefixEnd_4311225 2213730634680000046060543 := by
  unfold tailWord_4311225
  simp only [CollatzResearch.WordTrace]
  refine ⟨157243293806175598455383129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104828862537450398970255419 157243293806175598455383129)
  ·
    refine ⟨117932470354631698841537347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157243293806175598455383129 117932470354631698841537347)
    ·
      refine ⟨176898705531947548262306021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117932470354631698841537347 176898705531947548262306021)
      ·
        refine ⟨33168507287240165299182379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176898705531947548262306021 33168507287240165299182379)
        ·
          refine ⟨49752760930860247948773569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33168507287240165299182379 49752760930860247948773569)
          ·
            refine ⟨37314570698145185961580177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49752760930860247948773569 37314570698145185961580177)
            ·
              refine ⟨27985928023608889471185133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37314570698145185961580177 27985928023608889471185133)
              ·
                refine ⟨10494723008853333551694425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27985928023608889471185133 10494723008853333551694425)
                ·
                  refine ⟨7871042256640000163770819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10494723008853333551694425 7871042256640000163770819)
                  ·
                    refine ⟨11806563384960000245656229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7871042256640000163770819 11806563384960000245656229)
                    ·
                      refine ⟨2213730634680000046060543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11806563384960000245656229 2213730634680000046060543)
                      ·
                        rfl

theorem cell23_4311225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4311225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311225 prefixEnd_4311225 := by exact prefixLift 4311225
  have htrace : WordTrace (prefixWord ++ tailWord_4311225) baseStart_4311225 baseEnd_4311225 := by
    simpa [prefixWord, tailWord_4311225, baseEnd_4311225] using wordTrace_append hprefix tailTrace_4311225
  have hstable : (prefixWord ++ tailWord_4311225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311225).length < 2 ^ (prefixWord ++ tailWord_4311225).sum := by decide
  have hdescent : baseEnd_4311225 < baseStart_4311225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311265 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 6]
def baseStart_4311265 : Nat := 118140960795 + 4311265 * 2 ^ 59
def prefixEnd_4311265 : Nat := 4983230072969 + 3 ^ 40 * 4311265 * 2
def baseEnd_4311265 : Nat := 245972352656242209951151

theorem tailTrace_4311265 : CollatzResearch.WordTrace tailWord_4311265 prefixEnd_4311265 245972352656242209951151 := by
  unfold tailWord_4311265
  simp only [CollatzResearch.WordTrace]
  refine ⟨157244752726030685286839249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104829835150687123524559499 157244752726030685286839249)
  ·
    refine ⟨117933564544523013965129437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157244752726030685286839249 117933564544523013965129437)
    ·
      refine ⟨44225086704196130236923539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117933564544523013965129437 44225086704196130236923539)
      ·
        refine ⟨66337630056294195355385309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44225086704196130236923539 66337630056294195355385309)
        ·
          refine ⟨24876611271110323258269491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66337630056294195355385309 24876611271110323258269491)
          ·
            refine ⟨37314916906665484887404237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24876611271110323258269491 37314916906665484887404237)
            ·
              refine ⟨13993093839999556832776589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37314916906665484887404237 13993093839999556832776589)
              ·
                refine ⟨5247410189999833812291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13993093839999556832776589 5247410189999833812291221)
                ·
                  refine ⟨245972352656242209951151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5247410189999833812291221 245972352656242209951151)
                  ·
                    rfl

theorem cell23_4311265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_4311265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311265 prefixEnd_4311265 := by exact prefixLift 4311265
  have htrace : WordTrace (prefixWord ++ tailWord_4311265) baseStart_4311265 baseEnd_4311265 := by
    simpa [prefixWord, tailWord_4311265, baseEnd_4311265] using wordTrace_append hprefix tailTrace_4311265
  have hstable : (prefixWord ++ tailWord_4311265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311265).length < 2 ^ (prefixWord ++ tailWord_4311265).sum := by decide
  have hdescent : baseEnd_4311265 < baseStart_4311265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311288 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_4311288 : Nat := 118140960795 + 4311288 * 2 ^ 59
def prefixEnd_4311288 : Nat := 4983230072969 + 3 ^ 40 * 4311288 * 2
def baseEnd_4311288 : Nat := 2213762983961233299572753

theorem tailTrace_4311288 : CollatzResearch.WordTrace tailWord_4311288 prefixEnd_4311288 2213762983961233299572753 := by
  unfold tailWord_4311288
  simp only [CollatzResearch.WordTrace]
  refine ⟨78622795802473680107463259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104830394403298240143284345 78622795802473680107463259)
  ·
    refine ⟨117934193703710520161194889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78622795802473680107463259 117934193703710520161194889)
    ·
      refine ⟨88450645277782890120896167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117934193703710520161194889 88450645277782890120896167)
      ·
        refine ⟨132675967916674335181344251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88450645277782890120896167 132675967916674335181344251)
        ·
          refine ⟨199013951875011502772016377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132675967916674335181344251 199013951875011502772016377)
          ·
            refine ⟨149260463906258627079012283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199013951875011502772016377 149260463906258627079012283)
            ·
              refine ⟨223890695859387940618518425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149260463906258627079012283 223890695859387940618518425)
              ·
                refine ⟨167918021894540955463888819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223890695859387940618518425 167918021894540955463888819)
                ·
                  refine ⟨251877032841811433195833229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167918021894540955463888819 251877032841811433195833229)
                  ·
                    refine ⟨94453887315679287448437461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251877032841811433195833229 94453887315679287448437461)
                    ·
                      refine ⟨2213762983961233299572753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94453887315679287448437461 2213762983961233299572753)
                      ·
                        rfl

theorem cell23_4311288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_4311288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311288 prefixEnd_4311288 := by exact prefixLift 4311288
  have htrace : WordTrace (prefixWord ++ tailWord_4311288) baseStart_4311288 baseEnd_4311288 := by
    simpa [prefixWord, tailWord_4311288, baseEnd_4311288] using wordTrace_append hprefix tailTrace_4311288
  have hstable : (prefixWord ++ tailWord_4311288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311288).length < 2 ^ (prefixWord ++ tailWord_4311288).sum := by decide
  have hdescent : baseEnd_4311288 < baseStart_4311288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311326 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4311326 : Nat := 118140960795 + 4311326 * 2 ^ 59
def prefixEnd_4311326 : Nat := 4983230072969 + 3 ^ 40 * 4311326 * 2
def baseEnd_4311326 : Nat := 2213782496226104150897579

theorem tailTrace_4311326 : CollatzResearch.WordTrace tailWord_4311326 prefixEnd_4311326 2213782496226104150897579 := by
  unfold tailWord_4311326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19655872197351211588101229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104831318385873128469873221 19655872197351211588101229)
  ·
    refine ⟨7370952074006704345537961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19655872197351211588101229 7370952074006704345537961)
    ·
      refine ⟨5528214055505028259153471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7370952074006704345537961 5528214055505028259153471)
      ·
        refine ⟨8292321083257542388730207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5528214055505028259153471 8292321083257542388730207)
        ·
          refine ⟨12438481624886313583095311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292321083257542388730207 12438481624886313583095311)
          ·
            refine ⟨18657722437329470374642967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12438481624886313583095311 18657722437329470374642967)
            ·
              refine ⟨27986583655994205561964451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18657722437329470374642967 27986583655994205561964451)
              ·
                refine ⟨41979875483991308342946677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27986583655994205561964451 41979875483991308342946677)
                ·
                  refine ⟨3935613326624185157151251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41979875483991308342946677 3935613326624185157151251)
                  ·
                    refine ⟨5903419989936277735726877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935613326624185157151251 5903419989936277735726877)
                    ·
                      refine ⟨2213782496226104150897579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903419989936277735726877 2213782496226104150897579)
                      ·
                        rfl

theorem cell23_4311326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4311326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311326 prefixEnd_4311326 := by exact prefixLift 4311326
  have htrace : WordTrace (prefixWord ++ tailWord_4311326) baseStart_4311326 baseEnd_4311326 := by
    simpa [prefixWord, tailWord_4311326, baseEnd_4311326] using wordTrace_append hprefix tailTrace_4311326
  have hstable : (prefixWord ++ tailWord_4311326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311326).length < 2 ^ (prefixWord ++ tailWord_4311326).sum := by decide
  have hdescent : baseEnd_4311326 < baseStart_4311326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311332 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_4311332 : Nat := 118140960795 + 4311332 * 2 ^ 59
def prefixEnd_4311332 : Nat := 4983230072969 + 3 ^ 40 * 4311332 * 2
def baseEnd_4311332 : Nat := 2213785577110031127422551

theorem tailTrace_4311332 : CollatzResearch.WordTrace tailWord_4311332 prefixEnd_4311332 2213785577110031127422551 := by
  unfold tailWord_4311332
  simp only [CollatzResearch.WordTrace]
  refine ⟨78623598208393977864764125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104831464277858637153018833 78623598208393977864764125)
  ·
    refine ⟨29483849328147741699286547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78623598208393977864764125 29483849328147741699286547)
    ·
      refine ⟨44225773992221612548929821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29483849328147741699286547 44225773992221612548929821)
      ·
        refine ⟨16584665247083104705848683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44225773992221612548929821 16584665247083104705848683)
        ·
          refine ⟨24876997870624657058773025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16584665247083104705848683 24876997870624657058773025)
          ·
            refine ⟨18657748402968492794079769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24876997870624657058773025 18657748402968492794079769)
            ·
              refine ⟨13993311302226369595559827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18657748402968492794079769 13993311302226369595559827)
              ·
                refine ⟨20989966953339554393339741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13993311302226369595559827 20989966953339554393339741)
                ·
                  refine ⟨7871237607502332897502403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20989966953339554393339741 7871237607502332897502403)
                  ·
                    refine ⟨11806856411253499346253605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7871237607502332897502403 11806856411253499346253605)
                    ·
                      refine ⟨2213785577110031127422551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11806856411253499346253605 2213785577110031127422551)
                      ·
                        rfl

theorem cell23_4311332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_4311332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311332 prefixEnd_4311332 := by exact prefixLift 4311332
  have htrace : WordTrace (prefixWord ++ tailWord_4311332) baseStart_4311332 baseEnd_4311332 := by
    simpa [prefixWord, tailWord_4311332, baseEnd_4311332] using wordTrace_append hprefix tailTrace_4311332
  have hstable : (prefixWord ++ tailWord_4311332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311332).length < 2 ^ (prefixWord ++ tailWord_4311332).sum := by decide
  have hdescent : baseEnd_4311332 < baseStart_4311332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311346 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_4311346 : Nat := 118140960795 + 4311346 * 2 ^ 59
def prefixEnd_4311346 : Nat := 4983230072969 + 3 ^ 40 * 4311346 * 2
def baseEnd_4311346 : Nat := 737930921946398024215829

theorem tailTrace_4311346 : CollatzResearch.WordTrace tailWord_4311346 prefixEnd_4311346 737930921946398024215829 := by
  unfold tailWord_4311346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39311926759684309030134473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104831804692491490747025261 39311926759684309030134473)
  ·
    refine ⟨29483945069763231772600855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39311926759684309030134473 29483945069763231772600855)
    ·
      refine ⟨44225917604644847658901283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29483945069763231772600855 44225917604644847658901283)
      ·
        refine ⟨66338876406967271488351925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44225917604644847658901283 66338876406967271488351925)
        ·
          refine ⟨6219269663153181702032993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66338876406967271488351925 6219269663153181702032993)
          ·
            refine ⟨4664452247364886276524745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6219269663153181702032993 4664452247364886276524745)
            ·
              refine ⟨3498339185523664707393559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4664452247364886276524745 3498339185523664707393559)
              ·
                refine ⟨5247508778285497061090339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498339185523664707393559 5247508778285497061090339)
                ·
                  refine ⟨7871263167428245591635509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5247508778285497061090339 7871263167428245591635509)
                  ·
                    refine ⟨737930921946398024215829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7871263167428245591635509 737930921946398024215829)
                    ·
                      rfl

theorem cell23_4311346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_4311346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311346 prefixEnd_4311346 := by exact prefixLift 4311346
  have htrace : WordTrace (prefixWord ++ tailWord_4311346) baseStart_4311346 baseEnd_4311346 := by
    simpa [prefixWord, tailWord_4311346, baseEnd_4311346] using wordTrace_append hprefix tailTrace_4311346
  have hstable : (prefixWord ++ tailWord_4311346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311346).length < 2 ^ (prefixWord ++ tailWord_4311346).sum := by decide
  have hdescent : baseEnd_4311346 < baseStart_4311346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311349 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_4311349 : Nat := 118140960795 + 4311349 * 2 ^ 59
def prefixEnd_4311349 : Nat := 4983230072969 + 3 ^ 40 * 4311349 * 2
def baseEnd_4311349 : Nat := 2213794306281157560909973

theorem tailTrace_4311349 : CollatzResearch.WordTrace tailWord_4311349 prefixEnd_4311349 2213794306281157560909973 := by
  unfold tailWord_4311349
  simp only [CollatzResearch.WordTrace]
  refine ⟨157247816457726367632897101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104831877638484245088598067 157247816457726367632897101)
  ·
    refine ⟨58967931171647387862336413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157247816457726367632897101 58967931171647387862336413)
    ·
      refine ⟨22112974189367770448376155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58967931171647387862336413 22112974189367770448376155)
      ·
        refine ⟨33169461284051655672564233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22112974189367770448376155 33169461284051655672564233)
        ·
          refine ⟨24877095963038741754423175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33169461284051655672564233 24877095963038741754423175)
          ·
            refine ⟨37315643944558112631634763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24877095963038741754423175 37315643944558112631634763)
            ·
              refine ⟨55973465916837168947452145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37315643944558112631634763 55973465916837168947452145)
              ·
                refine ⟨41980099437627876710589109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55973465916837168947452145 41980099437627876710589109)
                ·
                  refine ⟨3935634322277613441617729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41980099437627876710589109 3935634322277613441617729)
                  ·
                    refine ⟨2951725741708210081213297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3935634322277613441617729 2951725741708210081213297)
                    ·
                      refine ⟨2213794306281157560909973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951725741708210081213297 2213794306281157560909973)
                      ·
                        rfl

theorem cell23_4311349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_4311349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311349 prefixEnd_4311349 := by exact prefixLift 4311349
  have htrace : WordTrace (prefixWord ++ tailWord_4311349) baseStart_4311349 baseEnd_4311349 := by
    simpa [prefixWord, tailWord_4311349, baseEnd_4311349] using wordTrace_append hprefix tailTrace_4311349
  have hstable : (prefixWord ++ tailWord_4311349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311349).length < 2 ^ (prefixWord ++ tailWord_4311349).sum := by decide
  have hdescent : baseEnd_4311349 < baseStart_4311349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311365 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_4311365 : Nat := 118140960795 + 4311365 * 2 ^ 59
def prefixEnd_4311365 : Nat := 4983230072969 + 3 ^ 40 * 4311365 * 2
def baseEnd_4311365 : Nat := 2213802521971629498309899

theorem tailTrace_4311365 : CollatzResearch.WordTrace tailWord_4311365 prefixEnd_4311365 2213802521971629498309899 := by
  unfold tailWord_4311365
  simp only [CollatzResearch.WordTrace]
  refine ⟨157248400025668402365479549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104832266683778934910319699 157248400025668402365479549)
  ·
    refine ⟨58968150009625650887054831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157248400025668402365479549 58968150009625650887054831)
    ·
      refine ⟨88452225014438476330582247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58968150009625650887054831 88452225014438476330582247)
      ·
        refine ⟨132678337521657714495873371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88452225014438476330582247 132678337521657714495873371)
        ·
          refine ⟨199017506282486571743810057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132678337521657714495873371 199017506282486571743810057)
          ·
            refine ⟨149263129711864928807857543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199017506282486571743810057 149263129711864928807857543)
            ·
              refine ⟨223894694567797393211786315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149263129711864928807857543 223894694567797393211786315)
              ·
                refine ⟨335842041851696089817679473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223894694567797393211786315 335842041851696089817679473)
                ·
                  refine ⟨251881531388772067363259605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335842041851696089817679473 251881531388772067363259605)
                  ·
                    refine ⟨5903473391924345328826397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 251881531388772067363259605 5903473391924345328826397)
                    ·
                      refine ⟨2213802521971629498309899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903473391924345328826397 2213802521971629498309899)
                      ·
                        rfl

theorem cell23_4311365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_4311365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311365 prefixEnd_4311365 := by exact prefixLift 4311365
  have htrace : WordTrace (prefixWord ++ tailWord_4311365) baseStart_4311365 baseEnd_4311365 := by
    simpa [prefixWord, tailWord_4311365, baseEnd_4311365] using wordTrace_append hprefix tailTrace_4311365
  have hstable : (prefixWord ++ tailWord_4311365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311365).length < 2 ^ (prefixWord ++ tailWord_4311365).sum := by decide
  have hdescent : baseEnd_4311365 < baseStart_4311365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311395 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_4311395 : Nat := 118140960795 + 4311395 * 2 ^ 59
def prefixEnd_4311395 : Nat := 4983230072969 + 3 ^ 40 * 4311395 * 2
def baseEnd_4311395 : Nat := 2213817926391264380934761

theorem tailTrace_4311395 : CollatzResearch.WordTrace tailWord_4311395 prefixEnd_4311395 2213817926391264380934761 := by
  unfold tailWord_4311395
  simp only [CollatzResearch.WordTrace]
  refine ⟨157249494215559717489071639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104832996143706478326047759 157249494215559717489071639)
  ·
    refine ⟨235874241323339576233607459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157249494215559717489071639 235874241323339576233607459)
    ·
      refine ⟨353811361985009364350411189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235874241323339576233607459 353811361985009364350411189)
      ·
        refine ⟨33169815186094627907851049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 353811361985009364350411189 33169815186094627907851049)
        ·
          refine ⟨24877361389570970930888287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33169815186094627907851049 24877361389570970930888287)
          ·
            refine ⟨37316042084356456396332431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24877361389570970930888287 37316042084356456396332431)
            ·
              refine ⟨55974063126534684594498647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37316042084356456396332431 55974063126534684594498647)
              ·
                refine ⟨83961094689802026891747971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55974063126534684594498647 83961094689802026891747971)
                ·
                  refine ⟨125941642034703040337621957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83961094689802026891747971 125941642034703040337621957)
                  ·
                    refine ⟨23614057881506820063304117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125941642034703040337621957 23614057881506820063304117)
                    ·
                      refine ⟨2213817926391264380934761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23614057881506820063304117 2213817926391264380934761)
                      ·
                        rfl

theorem cell23_4311395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_4311395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311395 prefixEnd_4311395 := by exact prefixLift 4311395
  have htrace : WordTrace (prefixWord ++ tailWord_4311395) baseStart_4311395 baseEnd_4311395 := by
    simpa [prefixWord, tailWord_4311395, baseEnd_4311395] using wordTrace_append hprefix tailTrace_4311395
  have hstable : (prefixWord ++ tailWord_4311395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311395).length < 2 ^ (prefixWord ++ tailWord_4311395).sum := by decide
  have hdescent : baseEnd_4311395 < baseStart_4311395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311399 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_4311399 : Nat := 118140960795 + 4311399 * 2 ^ 59
def prefixEnd_4311399 : Nat := 4983230072969 + 3 ^ 40 * 4311399 * 2
def baseEnd_4311399 : Nat := 2213819980313882365284743

theorem tailTrace_4311399 : CollatzResearch.WordTrace tailWord_4311399 prefixEnd_4311399 2213819980313882365284743 := by
  unfold tailWord_4311399
  simp only [CollatzResearch.WordTrace]
  refine ⟨157249640107545226172217251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104833093405030150781478167 157249640107545226172217251)
  ·
    refine ⟨235874460161317839258325877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157249640107545226172217251 235874460161317839258325877)
    ·
      refine ⟨22113230640123547430468051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235874460161317839258325877 22113230640123547430468051)
      ·
        refine ⟨33169845960185321145702077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22113230640123547430468051 33169845960185321145702077)
        ·
          refine ⟨12438692235069495429638279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33169845960185321145702077 12438692235069495429638279)
          ·
            refine ⟨18658038352604243144457419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12438692235069495429638279 18658038352604243144457419)
            ·
              refine ⟨27987057528906364716686129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18658038352604243144457419 27987057528906364716686129)
              ·
                refine ⟨20990293146679773537514597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27987057528906364716686129 20990293146679773537514597)
                ·
                  refine ⟨3935679965002457538283987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20990293146679773537514597 3935679965002457538283987)
                  ·
                    refine ⟨5903519947503686307425981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935679965002457538283987 5903519947503686307425981)
                    ·
                      refine ⟨2213819980313882365284743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903519947503686307425981 2213819980313882365284743)
                      ·
                        rfl

theorem cell23_4311399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_4311399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311399 prefixEnd_4311399 := by exact prefixLift 4311399
  have htrace : WordTrace (prefixWord ++ tailWord_4311399) baseStart_4311399 baseEnd_4311399 := by
    simpa [prefixWord, tailWord_4311399, baseEnd_4311399] using wordTrace_append hprefix tailTrace_4311399
  have hstable : (prefixWord ++ tailWord_4311399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311399).length < 2 ^ (prefixWord ++ tailWord_4311399).sum := by decide
  have hdescent : baseEnd_4311399 < baseStart_4311399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311400 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4311400 : Nat := 118140960795 + 4311400 * 2 ^ 59
def prefixEnd_4311400 : Nat := 4983230072969 + 3 ^ 40 * 4311400 * 2
def baseEnd_4311400 : Nat := 2213820493794536861372239

theorem tailTrace_4311400 : CollatzResearch.WordTrace tailWord_4311400 prefixEnd_4311400 2213820493794536861372239 := by
  unfold tailWord_4311400
  simp only [CollatzResearch.WordTrace]
  refine ⟨78624838290270801671501827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104833117720361068895335769 78624838290270801671501827)
  ·
    refine ⟨117937257435406202507252741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78624838290270801671501827 117937257435406202507252741)
    ·
      refine ⟨22113235769138662970109889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117937257435406202507252741 22113235769138662970109889)
      ·
        refine ⟨16584926826853997227582417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22113235769138662970109889 16584926826853997227582417)
        ·
          refine ⟨12438695120140497920686813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16584926826853997227582417 12438695120140497920686813)
          ·
            refine ⟨4664510670052686720257555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12438695120140497920686813 4664510670052686720257555)
            ·
              refine ⟨6996766005079030080386333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664510670052686720257555 6996766005079030080386333)
              ·
                refine ⟨2623787251904636280144875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6996766005079030080386333 2623787251904636280144875)
                ·
                  refine ⟨3935680877856954420217313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623787251904636280144875 3935680877856954420217313)
                  ·
                    refine ⟨2951760658392715815162985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3935680877856954420217313 2951760658392715815162985)
                    ·
                      refine ⟨2213820493794536861372239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951760658392715815162985 2213820493794536861372239)
                      ·
                        rfl

theorem cell23_4311400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4311400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311400 prefixEnd_4311400 := by exact prefixLift 4311400
  have htrace : WordTrace (prefixWord ++ tailWord_4311400) baseStart_4311400 baseEnd_4311400 := by
    simpa [prefixWord, tailWord_4311400, baseEnd_4311400] using wordTrace_append hprefix tailTrace_4311400
  have hstable : (prefixWord ++ tailWord_4311400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311400).length < 2 ^ (prefixWord ++ tailWord_4311400).sum := by decide
  have hdescent : baseEnd_4311400 < baseStart_4311400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311415 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 2, 6]
def baseStart_4311415 : Nat := 118140960795 + 4311415 * 2 ^ 59
def prefixEnd_4311415 : Nat := 4983230072969 + 3 ^ 40 * 4311415 * 2
def baseEnd_4311415 : Nat := 737942732001451434228223

theorem tailTrace_4311415 : CollatzResearch.WordTrace tailWord_4311415 prefixEnd_4311415 737942732001451434228223 := by
  unfold tailWord_4311415
  simp only [CollatzResearch.WordTrace]
  refine ⟨157250223675487260904799699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104833482450324840603199799 157250223675487260904799699)
  ·
    refine ⟨235875335513230891357199549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157250223675487260904799699 235875335513230891357199549)
    ·
      refine ⟨88453250817461584258949831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235875335513230891357199549 88453250817461584258949831)
      ·
        refine ⟨132679876226192376388424747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88453250817461584258949831 132679876226192376388424747)
        ·
          refine ⟨199019814339288564582637121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132679876226192376388424747 199019814339288564582637121)
          ·
            refine ⟨149264860754466423436977841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199019814339288564582637121 149264860754466423436977841)
            ·
              refine ⟨111948645565849817577733381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149264860754466423436977841 111948645565849817577733381)
              ·
                refine ⟨20990371043596840795825009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111948645565849817577733381 20990371043596840795825009)
                ·
                  refine ⟨15742778282697630596868757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20990371043596840795825009 15742778282697630596868757)
                  ·
                    refine ⟨737942732001451434228223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15742778282697630596868757 737942732001451434228223)
                    ·
                      rfl

theorem cell23_4311415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_4311415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311415 prefixEnd_4311415 := by exact prefixLift 4311415
  have htrace : WordTrace (prefixWord ++ tailWord_4311415) baseStart_4311415 baseEnd_4311415 := by
    simpa [prefixWord, tailWord_4311415, baseEnd_4311415] using wordTrace_append hprefix tailTrace_4311415
  have hstable : (prefixWord ++ tailWord_4311415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311415).length < 2 ^ (prefixWord ++ tailWord_4311415).sum := by decide
  have hdescent : baseEnd_4311415 < baseStart_4311415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311433 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 2, 1, 3]
def baseStart_4311433 : Nat := 118140960795 + 4311433 * 2 ^ 59
def prefixEnd_4311433 : Nat := 4983230072969 + 3 ^ 40 * 4311433 * 2
def baseEnd_4311433 : Nat := 2213837438656135232259587

theorem tailTrace_4311433 : CollatzResearch.WordTrace tailWord_4311433 prefixEnd_4311433 2213837438656135232259587 := by
  unfold tailWord_4311433
  simp only [CollatzResearch.WordTrace]
  refine ⟨157250880189422049978954953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104833920126281366652636635 157250880189422049978954953)
  ·
    refine ⟨117938160142066537484216215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157250880189422049978954953 117938160142066537484216215)
    ·
      refine ⟨176907240213099806226324323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117938160142066537484216215 176907240213099806226324323)
      ·
        refine ⟨265360860319649709339486485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176907240213099806226324323 265360860319649709339486485)
        ·
          refine ⟨12438790327483580125288429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 265360860319649709339486485 12438790327483580125288429)
          ·
            refine ⟨4664546372806342546983161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12438790327483580125288429 4664546372806342546983161)
            ·
              refine ⟨3498409779604756910237371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4664546372806342546983161 3498409779604756910237371)
              ·
                refine ⟨5247614669407135365356057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498409779604756910237371 5247614669407135365356057)
                ·
                  refine ⟨3935711002055351524017043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247614669407135365356057 3935711002055351524017043)
                  ·
                    refine ⟨5903566503083027286025565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935711002055351524017043 5903566503083027286025565)
                    ·
                      refine ⟨2213837438656135232259587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5903566503083027286025565 2213837438656135232259587)
                      ·
                        rfl

theorem cell23_4311433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 1, 3].length) (baseStart_4311433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311433 prefixEnd_4311433 := by exact prefixLift 4311433
  have htrace : WordTrace (prefixWord ++ tailWord_4311433) baseStart_4311433 baseEnd_4311433 := by
    simpa [prefixWord, tailWord_4311433, baseEnd_4311433] using wordTrace_append hprefix tailTrace_4311433
  have hstable : (prefixWord ++ tailWord_4311433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311433).length < 2 ^ (prefixWord ++ tailWord_4311433).sum := by decide
  have hdescent : baseEnd_4311433 < baseStart_4311433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311445 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 9]
def baseStart_4311445 : Nat := 118140960795 + 4311445 * 2 ^ 59
def prefixEnd_4311445 : Nat := 4983230072969 + 3 ^ 40 * 4311445 * 2
def baseEnd_4311445 : Nat := 245982622269332131701059

theorem tailTrace_4311445 : CollatzResearch.WordTrace tailWord_4311445 prefixEnd_4311445 245982622269332131701059 := by
  unfold tailWord_4311445
  simp only [CollatzResearch.WordTrace]
  refine ⟨157251317865378576028391789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104834211910252384018927859 157251317865378576028391789)
  ·
    refine ⟨58969244199516966010646921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157251317865378576028391789 58969244199516966010646921)
    ·
      refine ⟨44226933149637724507985191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58969244199516966010646921 44226933149637724507985191)
      ·
        refine ⟨66340399724456586761977787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44226933149637724507985191 66340399724456586761977787)
        ·
          refine ⟨99510599586684880142966681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66340399724456586761977787 99510599586684880142966681)
          ·
            refine ⟨74632949690013660107225011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99510599586684880142966681 74632949690013660107225011)
            ·
              refine ⟨111949424535020490160837517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74632949690013660107225011 111949424535020490160837517)
              ·
                refine ⟨41981034200632683810314069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111949424535020490160837517 41981034200632683810314069)
                ·
                  refine ⟨245982622269332131701059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41981034200632683810314069 245982622269332131701059)
                  ·
                    rfl

theorem cell23_4311445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_4311445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311445 prefixEnd_4311445 := by exact prefixLift 4311445
  have htrace : WordTrace (prefixWord ++ tailWord_4311445) baseStart_4311445 baseEnd_4311445 := by
    simpa [prefixWord, tailWord_4311445, baseEnd_4311445] using wordTrace_append hprefix tailTrace_4311445
  have hstable : (prefixWord ++ tailWord_4311445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311445).length < 2 ^ (prefixWord ++ tailWord_4311445).sum := by decide
  have hdescent : baseEnd_4311445 < baseStart_4311445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311473 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4311473 : Nat := 118140960795 + 4311473 * 2 ^ 59
def prefixEnd_4311473 : Nat := 4983230072969 + 3 ^ 40 * 4311473 * 2
def baseEnd_4311473 : Nat := 2213857977882315075759403

theorem tailTrace_4311473 : CollatzResearch.WordTrace tailWord_4311473 prefixEnd_4311473 2213857977882315075759403 := by
  unfold tailWord_4311473
  simp only [CollatzResearch.WordTrace]
  refine ⟨157252339109277136810411073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104834892739518091206940715 157252339109277136810411073)
  ·
    refine ⟨117939254331957852607808305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157252339109277136810411073 117939254331957852607808305)
    ·
      refine ⟨88454440748968389455856229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117939254331957852607808305 88454440748968389455856229)
      ·
        refine ⟨16585207640431573022973043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88454440748968389455856229 16585207640431573022973043)
        ·
          refine ⟨24877811460647359534459565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16585207640431573022973043 24877811460647359534459565)
          ·
            refine ⟨9329179297742759825422337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24877811460647359534459565 9329179297742759825422337)
            ·
              refine ⟨6996884473307069869066753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9329179297742759825422337 6996884473307069869066753)
              ·
                refine ⟨5247663354980302401800065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6996884473307069869066753 5247663354980302401800065)
                ·
                  refine ⟨3935747516235226801350049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247663354980302401800065 3935747516235226801350049)
                  ·
                    refine ⟨2951810637176420101012537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3935747516235226801350049 2951810637176420101012537)
                    ·
                      refine ⟨2213857977882315075759403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951810637176420101012537 2213857977882315075759403)
                      ·
                        rfl

theorem cell23_4311473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4311473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311473 prefixEnd_4311473 := by exact prefixLift 4311473
  have htrace : WordTrace (prefixWord ++ tailWord_4311473) baseStart_4311473 baseEnd_4311473 := by
    simpa [prefixWord, tailWord_4311473, baseEnd_4311473] using wordTrace_append hprefix tailTrace_4311473
  have hstable : (prefixWord ++ tailWord_4311473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311473).length < 2 ^ (prefixWord ++ tailWord_4311473).sum := by decide
  have hdescent : baseEnd_4311473 < baseStart_4311473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311475 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 7]
def baseStart_4311475 : Nat := 118140960795 + 4311475 * 2 ^ 59
def prefixEnd_4311475 : Nat := 4983230072969 + 3 ^ 40 * 4311475 * 2
def baseEnd_4311475 : Nat := 737953001614541355978131

theorem tailTrace_4311475 : CollatzResearch.WordTrace tailWord_4311475 prefixEnd_4311475 737953001614541355978131 := by
  unfold tailWord_4311475
  simp only [CollatzResearch.WordTrace]
  refine ⟨157252412055269891151983879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104834941370179927434655919 157252412055269891151983879)
  ·
    refine ⟨235878618082904836727975819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157252412055269891151983879 235878618082904836727975819)
    ·
      refine ⟨353817927124357255091963729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235878618082904836727975819 353817927124357255091963729)
      ·
        refine ⟨265363445343267941318972797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353817927124357255091963729 265363445343267941318972797)
        ·
          refine ⟨99511292003725477994614799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265363445343267941318972797 99511292003725477994614799)
          ·
            refine ⟨149266938005588216991922199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99511292003725477994614799 149266938005588216991922199)
            ·
              refine ⟨223900407008382325487883299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149266938005588216991922199 223900407008382325487883299)
              ·
                refine ⟨335850610512573488231824949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223900407008382325487883299 335850610512573488231824949)
                ·
                  refine ⟨31485994735553764521733589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 335850610512573488231824949 31485994735553764521733589)
                  ·
                    refine ⟨737953001614541355978131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31485994735553764521733589 737953001614541355978131)
                    ·
                      rfl

theorem cell23_4311475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_4311475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311475 prefixEnd_4311475 := by exact prefixLift 4311475
  have htrace : WordTrace (prefixWord ++ tailWord_4311475) baseStart_4311475 baseEnd_4311475 := by
    simpa [prefixWord, tailWord_4311475, baseEnd_4311475] using wordTrace_append hprefix tailTrace_4311475
  have hstable : (prefixWord ++ tailWord_4311475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311475).length < 2 ^ (prefixWord ++ tailWord_4311475).sum := by decide
  have hdescent : baseEnd_4311475 < baseStart_4311475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311479 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 5]
def baseStart_4311479 : Nat := 118140960795 + 4311479 * 2 ^ 59
def prefixEnd_4311479 : Nat := 4983230072969 + 3 ^ 40 * 4311479 * 2
def baseEnd_4311479 : Nat := 245984562085138005809375

theorem tailTrace_4311479 : CollatzResearch.WordTrace tailWord_4311479 prefixEnd_4311479 245984562085138005809375 := by
  unfold tailWord_4311479
  simp only [CollatzResearch.WordTrace]
  refine ⟨157252557947255399835129491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104835038631503599890086327 157252557947255399835129491)
  ·
    refine ⟨235878836920883099752694237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157252557947255399835129491 235878836920883099752694237)
    ·
      refine ⟨88454563845331162407260339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235878836920883099752694237 88454563845331162407260339)
      ·
        refine ⟨132681845767996743610890509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88454563845331162407260339 132681845767996743610890509)
        ·
          refine ⟨49755692162998778854083941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132681845767996743610890509 49755692162998778854083941)
          ·
            refine ⟨9329192280562271035140739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49755692162998778854083941 9329192280562271035140739)
            ·
              refine ⟨13993788420843406552711109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9329192280562271035140739 13993788420843406552711109)
              ·
                refine ⟨2623835328908138728633333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13993788420843406552711109 2623835328908138728633333)
                ·
                  refine ⟨245984562085138005809375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623835328908138728633333 245984562085138005809375)
                  ·
                    rfl

theorem cell23_4311479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 5].length) (baseStart_4311479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311479 prefixEnd_4311479 := by exact prefixLift 4311479
  have htrace : WordTrace (prefixWord ++ tailWord_4311479) baseStart_4311479 baseEnd_4311479 := by
    simpa [prefixWord, tailWord_4311479, baseEnd_4311479] using wordTrace_append hprefix tailTrace_4311479
  have hstable : (prefixWord ++ tailWord_4311479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311479).length < 2 ^ (prefixWord ++ tailWord_4311479).sum := by decide
  have hdescent : baseEnd_4311479 < baseStart_4311479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311509 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_4311509 : Nat := 118140960795 + 4311509 * 2 ^ 59
def prefixEnd_4311509 : Nat := 4983230072969 + 3 ^ 40 * 4311509 * 2
def baseEnd_4311509 : Nat := 737958821061958978303079

theorem tailTrace_4311509 : CollatzResearch.WordTrace tailWord_4311509 prefixEnd_4311509 737958821061958978303079 := by
  unfold tailWord_4311509
  simp only [CollatzResearch.WordTrace]
  refine ⟨157253652137146714958721581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104835768091431143305814387 157253652137146714958721581)
  ·
    refine ⟨58970119551430018109520593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157253652137146714958721581 58970119551430018109520593)
    ·
      refine ⟨44227589663572513582140445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58970119551430018109520593 44227589663572513582140445)
      ·
        refine ⟨16585346123839692593302667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44227589663572513582140445 16585346123839692593302667)
        ·
          refine ⟨24878019185759538889954001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16585346123839692593302667 24878019185759538889954001)
          ·
            refine ⟨18658514389319654167465501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24878019185759538889954001 18658514389319654167465501)
            ·
              refine ⟨6996942895994870312799563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18658514389319654167465501 6996942895994870312799563)
              ·
                refine ⟨10495414343992305469199345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6996942895994870312799563 10495414343992305469199345)
                ·
                  refine ⟨7871560757994229101899509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10495414343992305469199345 7871560757994229101899509)
                  ·
                    refine ⟨737958821061958978303079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7871560757994229101899509 737958821061958978303079)
                    ·
                      rfl

theorem cell23_4311509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_4311509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311509 prefixEnd_4311509 := by exact prefixLift 4311509
  have htrace : WordTrace (prefixWord ++ tailWord_4311509) baseStart_4311509 baseEnd_4311509 := by
    simpa [prefixWord, tailWord_4311509, baseEnd_4311509] using wordTrace_append hprefix tailTrace_4311509
  have hstable : (prefixWord ++ tailWord_4311509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311509).length < 2 ^ (prefixWord ++ tailWord_4311509).sum := by decide
  have hdescent : baseEnd_4311509 < baseStart_4311509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311539 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 3, 4]
def baseStart_4311539 : Nat := 118140960795 + 4311539 * 2 ^ 59
def prefixEnd_4311539 : Nat := 4983230072969 + 3 ^ 40 * 4311539 * 2
def baseEnd_4311539 : Nat := 737963955868503939178033

theorem tailTrace_4311539 : CollatzResearch.WordTrace tailWord_4311539 prefixEnd_4311539 737963955868503939178033 := by
  unfold tailWord_4311539
  simp only [CollatzResearch.WordTrace]
  refine ⟨157254746327038030082313671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104836497551358686721542447 157254746327038030082313671)
  ·
    refine ⟨235882119490557045123470507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157254746327038030082313671 235882119490557045123470507)
    ·
      refine ⟨353823179235835567685205761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235882119490557045123470507 353823179235835567685205761)
      ·
        refine ⟨265367384426876675763904321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353823179235835567685205761 265367384426876675763904321)
        ·
          refine ⟨199025538320157506822928241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265367384426876675763904321 199025538320157506822928241)
          ·
            refine ⟨149269153740118130117196181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199025538320157506822928241 149269153740118130117196181)
            ·
              refine ⟨6996991581568037349243571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149269153740118130117196181 6996991581568037349243571)
              ·
                refine ⟨10495487372352056023865357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6996991581568037349243571 10495487372352056023865357)
                ·
                  refine ⟨3935807764632021008949509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10495487372352056023865357 3935807764632021008949509)
                  ·
                    refine ⟨737963955868503939178033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935807764632021008949509 737963955868503939178033)
                    ·
                      rfl

theorem cell23_4311539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 4].length) (baseStart_4311539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311539 prefixEnd_4311539 := by exact prefixLift 4311539
  have htrace : WordTrace (prefixWord ++ tailWord_4311539) baseStart_4311539 baseEnd_4311539 := by
    simpa [prefixWord, tailWord_4311539, baseEnd_4311539] using wordTrace_append hprefix tailTrace_4311539
  have hstable : (prefixWord ++ tailWord_4311539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311539).length < 2 ^ (prefixWord ++ tailWord_4311539).sum := by decide
  have hdescent : baseEnd_4311539 < baseStart_4311539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311556 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_4311556 : Nat := 118140960795 + 4311556 * 2 ^ 59
def prefixEnd_4311556 : Nat := 4983230072969 + 3 ^ 40 * 4311556 * 2
def baseEnd_4311556 : Nat := 737966865592212750340507

theorem tailTrace_4311556 : CollatzResearch.WordTrace tailWord_4311556 prefixEnd_4311556 737966865592212750340507 := by
  unfold tailWord_4311556
  simp only [CollatzResearch.WordTrace]
  refine ⟨78627683183988220992841261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104836910911984294657121681 78627683183988220992841261)
  ·
    refine ⟨29485381193995582872315473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78627683183988220992841261 29485381193995582872315473)
    ·
      refine ⟨22114035895496687154236605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29485381193995582872315473 22114035895496687154236605)
      ·
        refine ⟨8292763460811257682838727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22114035895496687154236605 8292763460811257682838727)
        ·
          refine ⟨12439145191216886524258091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292763460811257682838727 12439145191216886524258091)
          ·
            refine ⟨18658717786825329786387137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12439145191216886524258091 18658717786825329786387137)
            ·
              refine ⟨13994038340118997339790353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18658717786825329786387137 13994038340118997339790353)
              ·
                refine ⟨10495528755089248004842765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13994038340118997339790353 10495528755089248004842765)
                ·
                  refine ⟨3935823283158468001816037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10495528755089248004842765 3935823283158468001816037)
                  ·
                    refine ⟨737966865592212750340507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3935823283158468001816037 737966865592212750340507)
                    ·
                      rfl

theorem cell23_4311556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_4311556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311556 prefixEnd_4311556 := by exact prefixLift 4311556
  have htrace : WordTrace (prefixWord ++ tailWord_4311556) baseStart_4311556 baseEnd_4311556 := by
    simpa [prefixWord, tailWord_4311556, baseEnd_4311556] using wordTrace_append hprefix tailTrace_4311556
  have hstable : (prefixWord ++ tailWord_4311556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311556).length < 2 ^ (prefixWord ++ tailWord_4311556).sum := by decide
  have hdescent : baseEnd_4311556 < baseStart_4311556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311619 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 6, 2]
def baseStart_4311619 : Nat := 118140960795 + 4311619 * 2 ^ 59
def prefixEnd_4311619 : Nat := 4983230072969 + 3 ^ 40 * 4311619 * 2
def baseEnd_4311619 : Nat := 2213932946057871504533731

theorem tailTrace_4311619 : CollatzResearch.WordTrace tailWord_4311619 prefixEnd_4311619 2213932946057871504533731 := by
  unfold tailWord_4311619
  simp only [CollatzResearch.WordTrace]
  refine ⟨157257664166748203745225911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104838442777832135830150607 157257664166748203745225911)
  ·
    refine ⟨235886496250122305617838867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157257664166748203745225911 235886496250122305617838867)
    ·
      refine ⟨353829744375183458426758301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235886496250122305617838867 353829744375183458426758301)
      ·
        refine ⟨132686154140693796910034363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353829744375183458426758301 132686154140693796910034363)
        ·
          refine ⟨199029231211040695365051545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132686154140693796910034363 199029231211040695365051545)
          ·
            refine ⟨149271923408280521523788659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199029231211040695365051545 149271923408280521523788659)
            ·
              refine ⟨223907885112420782285682989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149271923408280521523788659 223907885112420782285682989)
              ·
                refine ⟨83965456917157793357131121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223907885112420782285682989 83965456917157793357131121)
                ·
                  refine ⟨62974092687868345017848341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83965456917157793357131121 62974092687868345017848341)
                  ·
                    refine ⟨2951910594743828672711641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62974092687868345017848341 2951910594743828672711641)
                    ·
                      refine ⟨2213932946057871504533731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951910594743828672711641 2213932946057871504533731)
                      ·
                        rfl

theorem cell23_4311619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_4311619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311619 prefixEnd_4311619 := by exact prefixLift 4311619
  have htrace : WordTrace (prefixWord ++ tailWord_4311619) baseStart_4311619 baseEnd_4311619 := by
    simpa [prefixWord, tailWord_4311619, baseEnd_4311619] using wordTrace_append hprefix tailTrace_4311619
  have hstable : (prefixWord ++ tailWord_4311619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311619).length < 2 ^ (prefixWord ++ tailWord_4311619).sum := by decide
  have hdescent : baseEnd_4311619 < baseStart_4311619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311623 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_4311623 : Nat := 118140960795 + 4311623 * 2 ^ 59
def prefixEnd_4311623 : Nat := 4983230072969 + 3 ^ 40 * 4311623 * 2
def baseEnd_4311623 : Nat := 2213934999980489488883713

theorem tailTrace_4311623 : CollatzResearch.WordTrace tailWord_4311623 prefixEnd_4311623 2213934999980489488883713 := by
  unfold tailWord_4311623
  simp only [CollatzResearch.WordTrace]
  refine ⟨157257810058733712428371523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104838540039155808285581015 157257810058733712428371523)
  ·
    refine ⟨235886715088100568642557285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157257810058733712428371523 235886715088100568642557285)
    ·
      refine ⟨44228759079018856620479491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235886715088100568642557285 44228759079018856620479491)
      ·
        refine ⟨66343138618528284930719237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44228759079018856620479491 66343138618528284930719237)
        ·
          refine ⟨12439338490974053424509857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66343138618528284930719237 12439338490974053424509857)
          ·
            refine ⟨9329503868230540068382393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12439338490974053424509857 9329503868230540068382393)
            ·
              refine ⟨6997127901172905051286795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9329503868230540068382393 6997127901172905051286795)
              ·
                refine ⟨10495691851759357576930193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6997127901172905051286795 10495691851759357576930193)
                ·
                  refine ⟨7871768888819518182697645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10495691851759357576930193 7871768888819518182697645)
                  ·
                    refine ⟨2951913333307319318511617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7871768888819518182697645 2951913333307319318511617)
                    ·
                      refine ⟨2213934999980489488883713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951913333307319318511617 2213934999980489488883713)
                      ·
                        rfl

theorem cell23_4311623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_4311623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311623 prefixEnd_4311623 := by exact prefixLift 4311623
  have htrace : WordTrace (prefixWord ++ tailWord_4311623) baseStart_4311623 baseEnd_4311623 := by
    simpa [prefixWord, tailWord_4311623, baseEnd_4311623] using wordTrace_append hprefix tailTrace_4311623
  have hstable : (prefixWord ++ tailWord_4311623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311623).length < 2 ^ (prefixWord ++ tailWord_4311623).sum := by decide
  have hdescent : baseEnd_4311623 < baseStart_4311623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311632 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_4311632 : Nat := 118140960795 + 4311632 * 2 ^ 59
def prefixEnd_4311632 : Nat := 4983230072969 + 3 ^ 40 * 4311632 * 2
def baseEnd_4311632 : Nat := 2213939621306379953671171

theorem tailTrace_4311632 : CollatzResearch.WordTrace tailWord_4311632 prefixEnd_4311632 2213939621306379953671171 := by
  unfold tailWord_4311632
  simp only [CollatzResearch.WordTrace]
  refine ⟨78629069157850553482724575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104838758877134071310299433 78629069157850553482724575)
  ·
    refine ⟨117943603736775830224086863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78629069157850553482724575 117943603736775830224086863)
    ·
      refine ⟨176915405605163745336130295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117943603736775830224086863 176915405605163745336130295)
      ·
        refine ⟨265373108407745618004195443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176915405605163745336130295 265373108407745618004195443)
        ·
          refine ⟨398059662611618427006293165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265373108407745618004195443 398059662611618427006293165)
          ·
            refine ⟨149272373479356910127359937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398059662611618427006293165 149272373479356910127359937)
            ·
              refine ⟨111954280109517682595519953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149272373479356910127359937 111954280109517682595519953)
              ·
                refine ⟨83965710082138261946639965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111954280109517682595519953 83965710082138261946639965)
                ·
                  refine ⟨31487141280801848229989987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83965710082138261946639965 31487141280801848229989987)
                  ·
                    refine ⟨47230711921202772344984981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31487141280801848229989987 47230711921202772344984981)
                    ·
                      refine ⟨2213939621306379953671171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47230711921202772344984981 2213939621306379953671171)
                      ·
                        rfl

theorem cell23_4311632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_4311632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311632 prefixEnd_4311632 := by exact prefixLift 4311632
  have htrace : WordTrace (prefixWord ++ tailWord_4311632) baseStart_4311632 baseEnd_4311632 := by
    simpa [prefixWord, tailWord_4311632, baseEnd_4311632] using wordTrace_append hprefix tailTrace_4311632
  have hstable : (prefixWord ++ tailWord_4311632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311632).length < 2 ^ (prefixWord ++ tailWord_4311632).sum := by decide
  have hdescent : baseEnd_4311632 < baseStart_4311632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311709 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4311709 : Nat := 118140960795 + 4311709 * 2 ^ 59
def prefixEnd_4311709 : Nat := 4983230072969 + 3 ^ 40 * 4311709 * 2
def baseEnd_4311709 : Nat := 2213979159316776152408317

theorem tailTrace_4311709 : CollatzResearch.WordTrace tailWord_4311709 prefixEnd_4311709 2213979159316776152408317 := by
  unfold tailWord_4311709
  simp only [CollatzResearch.WordTrace]
  refine ⟨157260946736422149116002181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104840631157614766077334787 157260946736422149116002181)
  ·
    refine ⟨29486427513079152959250409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157260946736422149116002181 29486427513079152959250409)
    ·
      refine ⟨22114820634809364719437807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29486427513079152959250409 22114820634809364719437807)
      ·
        refine ⟨33172230952214047079156711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22114820634809364719437807 33172230952214047079156711)
        ·
          refine ⟨49758346428321070618735067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33172230952214047079156711 49758346428321070618735067)
          ·
            refine ⟨74637519642481605928102601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49758346428321070618735067 74637519642481605928102601)
            ·
              refine ⟨55978139731861204446076951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74637519642481605928102601 55978139731861204446076951)
              ·
                refine ⟨83967209597791806669115427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55978139731861204446076951 83967209597791806669115427)
                ·
                  refine ⟨125950814396687710003673141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83967209597791806669115427 125950814396687710003673141)
                  ·
                    refine ⟨11807888849689472812844357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125950814396687710003673141 11807888849689472812844357)
                    ·
                      refine ⟨2213979159316776152408317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11807888849689472812844357 2213979159316776152408317)
                      ·
                        rfl

theorem cell23_4311709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4311709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311709 prefixEnd_4311709 := by exact prefixLift 4311709
  have htrace : WordTrace (prefixWord ++ tailWord_4311709) baseStart_4311709 baseEnd_4311709 := by
    simpa [prefixWord, tailWord_4311709, baseEnd_4311709] using wordTrace_append hprefix tailTrace_4311709
  have hstable : (prefixWord ++ tailWord_4311709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311709).length < 2 ^ (prefixWord ++ tailWord_4311709).sum := by decide
  have hdescent : baseEnd_4311709 < baseStart_4311709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311743 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 4, 2, 2]
def baseStart_4311743 : Nat := 118140960795 + 4311743 * 2 ^ 59
def prefixEnd_4311743 : Nat := 4983230072969 + 3 ^ 40 * 4311743 * 2
def baseEnd_4311743 : Nat := 2213996617659029019383161

theorem tailTrace_4311743 : CollatzResearch.WordTrace tailWord_4311743 prefixEnd_4311743 2213996617659029019383161 := by
  unfold tailWord_4311743
  simp only [CollatzResearch.WordTrace]
  refine ⟨157262186818298972922739883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104841457878865981948493255 157262186818298972922739883)
  ·
    refine ⟨235893280227448459384109825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157262186818298972922739883 235893280227448459384109825)
    ·
      refine ⟨176919960170586344538082369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235893280227448459384109825 176919960170586344538082369)
      ·
        refine ⟨132689970127939758403561777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176919960170586344538082369 132689970127939758403561777)
        ·
          refine ⟨99517477595954818802671333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132689970127939758403561777 99517477595954818802671333)
          ·
            refine ⟨18659527049241528525500875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99517477595954818802671333 18659527049241528525500875)
            ·
              refine ⟨27989290573862292788251313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18659527049241528525500875 27989290573862292788251313)
              ·
                refine ⟨20991967930396719591188485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27989290573862292788251313 20991967930396719591188485)
                ·
                  refine ⟨3935993986949384923347841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20991967930396719591188485 3935993986949384923347841)
                  ·
                    refine ⟨2951995490212038692510881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3935993986949384923347841 2951995490212038692510881)
                    ·
                      refine ⟨2213996617659029019383161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2951995490212038692510881 2213996617659029019383161)
                      ·
                        rfl

theorem cell23_4311743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_4311743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311743 prefixEnd_4311743 := by exact prefixLift 4311743
  have htrace : WordTrace (prefixWord ++ tailWord_4311743) baseStart_4311743 baseEnd_4311743 := by
    simpa [prefixWord, tailWord_4311743, baseEnd_4311743] using wordTrace_append hprefix tailTrace_4311743
  have hstable : (prefixWord ++ tailWord_4311743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311743).length < 2 ^ (prefixWord ++ tailWord_4311743).sum := by decide
  have hdescent : baseEnd_4311743 < baseStart_4311743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311777 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_4311777 : Nat := 118140960795 + 4311777 * 2 ^ 59
def prefixEnd_4311777 : Nat := 4983230072969 + 3 ^ 40 * 4311777 * 2
def baseEnd_4311777 : Nat := 2214014076001281886358005

theorem tailTrace_4311777 : CollatzResearch.WordTrace tailWord_4311777 prefixEnd_4311777 2214014076001281886358005 := by
  unfold tailWord_4311777
  simp only [CollatzResearch.WordTrace]
  refine ⟨157263426900175796729477585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104842284600117197819651723 157263426900175796729477585)
  ·
    refine ⟨117947570175131847547108189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157263426900175796729477585 117947570175131847547108189)
    ·
      refine ⟨44230338815674442830165571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117947570175131847547108189 44230338815674442830165571)
      ·
        refine ⟨66345508223511664245248357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44230338815674442830165571 66345508223511664245248357)
        ·
          refine ⟨12439782791908437045984067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66345508223511664245248357 12439782791908437045984067)
          ·
            refine ⟨18659674187862655568976101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12439782791908437045984067 18659674187862655568976101)
            ·
              refine ⟨3498688910224247919183019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18659674187862655568976101 3498688910224247919183019)
              ·
                refine ⟨5248033365336371878774529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498688910224247919183019 5248033365336371878774529)
                ·
                  refine ⟨3936025024002278909080897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5248033365336371878774529 3936025024002278909080897)
                  ·
                    refine ⟨2952018768001709181810673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3936025024002278909080897 2952018768001709181810673)
                    ·
                      refine ⟨2214014076001281886358005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952018768001709181810673 2214014076001281886358005)
                      ·
                        rfl

theorem cell23_4311777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_4311777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311777 prefixEnd_4311777 := by exact prefixLift 4311777
  have htrace : WordTrace (prefixWord ++ tailWord_4311777) baseStart_4311777 baseEnd_4311777 := by
    simpa [prefixWord, tailWord_4311777, baseEnd_4311777] using wordTrace_append hprefix tailTrace_4311777
  have hstable : (prefixWord ++ tailWord_4311777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311777).length < 2 ^ (prefixWord ++ tailWord_4311777).sum := by decide
  have hdescent : baseEnd_4311777 < baseStart_4311777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311819 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_4311819 : Nat := 118140960795 + 4311819 * 2 ^ 59
def prefixEnd_4311819 : Nat := 4983230072969 + 3 ^ 40 * 4311819 * 2
def baseEnd_4311819 : Nat := 2214035642188770722032811

theorem tailTrace_4311819 : CollatzResearch.WordTrace tailWord_4311819 prefixEnd_4311819 2214035642188770722032811 := by
  unfold tailWord_4311819
  simp only [CollatzResearch.WordTrace]
  refine ⟨157264958766023637902506511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104843305844015758601671007 157264958766023637902506511)
  ·
    refine ⟨235897438149035456853759767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157264958766023637902506511 235897438149035456853759767)
    ·
      refine ⟨353846157223553185280639651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235897438149035456853759767 353846157223553185280639651)
      ·
        refine ⟨530769235835329777920959477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353846157223553185280639651 530769235835329777920959477)
        ·
          refine ⟨49759615859562166680089951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 530769235835329777920959477 49759615859562166680089951)
          ·
            refine ⟨74639423789343250020134927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49759615859562166680089951 74639423789343250020134927)
            ·
              refine ⟨111959135684014875030202391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74639423789343250020134927 111959135684014875030202391)
              ·
                refine ⟨167938703526022312545303587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111959135684014875030202391 167938703526022312545303587)
                ·
                  refine ⟨251908055289033468817955381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167938703526022312545303587 251908055289033468817955381)
                  ·
                    refine ⟨23616380183346887701683317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 251908055289033468817955381 23616380183346887701683317)
                    ·
                      refine ⟨2214035642188770722032811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23616380183346887701683317 2214035642188770722032811)
                      ·
                        rfl

theorem cell23_4311819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_4311819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311819 prefixEnd_4311819 := by exact prefixLift 4311819
  have htrace : WordTrace (prefixWord ++ tailWord_4311819) baseStart_4311819 baseEnd_4311819 := by
    simpa [prefixWord, tailWord_4311819, baseEnd_4311819] using wordTrace_append hprefix tailTrace_4311819
  have hstable : (prefixWord ++ tailWord_4311819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311819).length < 2 ^ (prefixWord ++ tailWord_4311819).sum := by decide
  have hdescent : baseEnd_4311819 < baseStart_4311819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311850 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4311850 : Nat := 118140960795 + 4311850 * 2 ^ 59
def prefixEnd_4311850 : Nat := 4983230072969 + 3 ^ 40 * 4311850 * 2
def baseEnd_4311850 : Nat := 2214051560089060100745169

theorem tailTrace_4311850 : CollatzResearch.WordTrace tailWord_4311850 prefixEnd_4311850 2214051560089060100745169 := by
  unfold tailWord_4311850
  simp only [CollatzResearch.WordTrace]
  refine ⟨39316522357227832549221251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104844059619274220131256669 39316522357227832549221251)
  ·
    refine ⟨58974783535841748823831877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39316522357227832549221251 58974783535841748823831877)
    ·
      refine ⟨11057771912970327904468477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58974783535841748823831877 11057771912970327904468477)
      ·
        refine ⟨4146664467363872964175679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11057771912970327904468477 4146664467363872964175679)
        ·
          refine ⟨6219996701045809446263519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4146664467363872964175679 6219996701045809446263519)
          ·
            refine ⟨9329995051568714169395279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219996701045809446263519 9329995051568714169395279)
            ·
              refine ⟨13994992577353071254092919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9329995051568714169395279 13994992577353071254092919)
              ·
                refine ⟨20992488866029606881139379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13994992577353071254092919 20992488866029606881139379)
                ·
                  refine ⟨31488733299044410321709069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20992488866029606881139379 31488733299044410321709069)
                  ·
                    refine ⟨11808274987141653870640901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31488733299044410321709069 11808274987141653870640901)
                    ·
                      refine ⟨2214051560089060100745169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11808274987141653870640901 2214051560089060100745169)
                      ·
                        rfl

theorem cell23_4311850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4311850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311850 prefixEnd_4311850 := by exact prefixLift 4311850
  have htrace : WordTrace (prefixWord ++ tailWord_4311850) baseStart_4311850 baseEnd_4311850 := by
    simpa [prefixWord, tailWord_4311850, baseEnd_4311850] using wordTrace_append hprefix tailTrace_4311850
  have hstable : (prefixWord ++ tailWord_4311850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311850).length < 2 ^ (prefixWord ++ tailWord_4311850).sum := by decide
  have hdescent : baseEnd_4311850 < baseStart_4311850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311886 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_4311886 : Nat := 118140960795 + 4311886 * 2 ^ 59
def prefixEnd_4311886 : Nat := 4983230072969 + 3 ^ 40 * 4311886 * 2
def baseEnd_4311886 : Nat := 738023348464207319965001

theorem tailTrace_4311886 : CollatzResearch.WordTrace tailWord_4311886 prefixEnd_4311886 738023348464207319965001 := by
  unfold tailWord_4311886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19658425307097613543149439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104844934971187272230130341 19658425307097613543149439)
  ·
    refine ⟨29487637960646420314724159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19658425307097613543149439 29487637960646420314724159)
    ·
      refine ⟨44231456940969630472086239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29487637960646420314724159 44231456940969630472086239)
      ·
        refine ⟨66347185411454445708129359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44231456940969630472086239 66347185411454445708129359)
        ·
          refine ⟨99520778117181668562194039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66347185411454445708129359 99520778117181668562194039)
          ·
            refine ⟨149281167175772502843291059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99520778117181668562194039 149281167175772502843291059)
            ·
              refine ⟨223921750763658754264936589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149281167175772502843291059 223921750763658754264936589)
              ·
                refine ⟨83970656536372032849351221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223921750763658754264936589 83970656536372032849351221)
                ·
                  refine ⟨7872249050284878079626677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83970656536372032849351221 7872249050284878079626677)
                  ·
                    refine ⟨738023348464207319965001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872249050284878079626677 738023348464207319965001)
                    ·
                      rfl

theorem cell23_4311886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_4311886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311886 prefixEnd_4311886 := by exact prefixLift 4311886
  have htrace : WordTrace (prefixWord ++ tailWord_4311886) baseStart_4311886 baseEnd_4311886 := by
    simpa [prefixWord, tailWord_4311886, baseEnd_4311886] using wordTrace_append hprefix tailTrace_4311886
  have hstable : (prefixWord ++ tailWord_4311886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311886).length < 2 ^ (prefixWord ++ tailWord_4311886).sum := by decide
  have hdescent : baseEnd_4311886 < baseStart_4311886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311893 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4311893 : Nat := 118140960795 + 4311893 * 2 ^ 59
def prefixEnd_4311893 : Nat := 4983230072969 + 3 ^ 40 * 4311893 * 2
def baseEnd_4311893 : Nat := 2214073639757203432507471

theorem tailTrace_4311893 : CollatzResearch.WordTrace tailWord_4311893 prefixEnd_4311893 2214073639757203432507471 := by
  unfold tailWord_4311893
  simp only [CollatzResearch.WordTrace]
  refine ⟨157267657767755548540700333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104845105178503699027133555 157267657767755548540700333)
  ·
    refine ⟨58975371662908330702762625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157267657767755548540700333 58975371662908330702762625)
    ·
      refine ⟨44231528747181248027071969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58975371662908330702762625 44231528747181248027071969)
      ·
        refine ⟨33173646560385936020303977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44231528747181248027071969 33173646560385936020303977)
        ·
          refine ⟨24880234920289452015227983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33173646560385936020303977 24880234920289452015227983)
          ·
            refine ⟨37320352380434178022841975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24880234920289452015227983 37320352380434178022841975)
            ·
              refine ⟨55980528570651267034262963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37320352380434178022841975 55980528570651267034262963)
              ·
                refine ⟨83970792855976900551394445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55980528570651267034262963 83970792855976900551394445)
                ·
                  refine ⟨31489047320991337706772917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83970792855976900551394445 31489047320991337706772917)
                  ·
                    refine ⟨2952098186342937910009961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31489047320991337706772917 2952098186342937910009961)
                    ·
                      refine ⟨2214073639757203432507471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952098186342937910009961 2214073639757203432507471)
                      ·
                        rfl

theorem cell23_4311893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4311893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311893 prefixEnd_4311893 := by exact prefixLift 4311893
  have htrace : WordTrace (prefixWord ++ tailWord_4311893) baseStart_4311893 baseEnd_4311893 := by
    simpa [prefixWord, tailWord_4311893, baseEnd_4311893] using wordTrace_append hprefix tailTrace_4311893
  have hstable : (prefixWord ++ tailWord_4311893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311893).length < 2 ^ (prefixWord ++ tailWord_4311893).sum := by decide
  have hdescent : baseEnd_4311893 < baseStart_4311893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311903 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 1, 5]
def baseStart_4311903 : Nat := 118140960795 + 4311903 * 2 ^ 59
def prefixEnd_4311903 : Nat := 4983230072969 + 3 ^ 40 * 4311903 * 2
def baseEnd_4311903 : Nat := 738026258187916131127475

theorem tailTrace_4311903 : CollatzResearch.WordTrace tailWord_4311903 prefixEnd_4311903 738026258187916131127475 := by
  unfold tailWord_4311903
  simp only [CollatzResearch.WordTrace]
  refine ⟨157268022497719320248564363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104845348331812880165709575 157268022497719320248564363)
  ·
    refine ⟨235902033746578980372846545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157268022497719320248564363 235902033746578980372846545)
    ·
      refine ⟨176926525309934235279634909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235902033746578980372846545 176926525309934235279634909)
      ·
        refine ⟨66347446991225338229863091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176926525309934235279634909 66347446991225338229863091)
        ·
          refine ⟨99521170486838007344794637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66347446991225338229863091 99521170486838007344794637)
          ·
            refine ⟨37320438932564252754297989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99521170486838007344794637 37320438932564252754297989)
            ·
              refine ⟨6997582299855797391430873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37320438932564252754297989 6997582299855797391430873)
              ·
                refine ⟨5248186724891848043573155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6997582299855797391430873 5248186724891848043573155)
                ·
                  refine ⟨7872280087337772065359733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248186724891848043573155 7872280087337772065359733)
                  ·
                    refine ⟨738026258187916131127475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872280087337772065359733 738026258187916131127475)
                    ·
                      rfl

theorem cell23_4311903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_4311903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311903 prefixEnd_4311903 := by exact prefixLift 4311903
  have htrace : WordTrace (prefixWord ++ tailWord_4311903) baseStart_4311903 baseEnd_4311903 := by
    simpa [prefixWord, tailWord_4311903, baseEnd_4311903] using wordTrace_append hprefix tailTrace_4311903
  have hstable : (prefixWord ++ tailWord_4311903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311903).length < 2 ^ (prefixWord ++ tailWord_4311903).sum := by decide
  have hdescent : baseEnd_4311903 < baseStart_4311903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311916 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_4311916 : Nat := 118140960795 + 4311916 * 2 ^ 59
def prefixEnd_4311916 : Nat := 4983230072969 + 3 ^ 40 * 4311916 * 2
def baseEnd_4311916 : Nat := 738028483270752280839955

theorem tailTrace_4311916 : CollatzResearch.WordTrace tailWord_4311916 prefixEnd_4311916 738028483270752280839955 := by
  unfold tailWord_4311916
  simp only [CollatzResearch.WordTrace]
  refine ⟨78634248323336111734393801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104845664431114815645858401 78634248323336111734393801)
  ·
    refine ⟨58975686242502083800795351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78634248323336111734393801 58975686242502083800795351)
    ·
      refine ⟨88463529363753125701193027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58975686242502083800795351 88463529363753125701193027)
      ·
        refine ⟨132695294045629688551789541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88463529363753125701193027 132695294045629688551789541)
        ·
          refine ⟨24880367633555566603460539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132695294045629688551789541 24880367633555566603460539)
          ·
            refine ⟨37320551450333349905190809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24880367633555566603460539 37320551450333349905190809)
            ·
              refine ⟨27990413587750012428893107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37320551450333349905190809 27990413587750012428893107)
              ·
                refine ⟨41985620381625018643339661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27990413587750012428893107 41985620381625018643339661)
                ·
                  refine ⟨15744607643109381991252373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41985620381625018643339661 15744607643109381991252373)
                  ·
                    refine ⟨738028483270752280839955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15744607643109381991252373 738028483270752280839955)
                    ·
                      rfl

theorem cell23_4311916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_4311916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311916 prefixEnd_4311916 := by exact prefixLift 4311916
  have htrace : WordTrace (prefixWord ++ tailWord_4311916) baseStart_4311916 baseEnd_4311916 := by
    simpa [prefixWord, tailWord_4311916, baseEnd_4311916] using wordTrace_append hprefix tailTrace_4311916
  have hstable : (prefixWord ++ tailWord_4311916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311916).length < 2 ^ (prefixWord ++ tailWord_4311916).sum := by decide
  have hdescent : baseEnd_4311916 < baseStart_4311916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311923 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 4]
def baseStart_4311923 : Nat := 118140960795 + 4311923 * 2 ^ 59
def prefixEnd_4311923 : Nat := 4983230072969 + 3 ^ 40 * 4311923 * 2
def baseEnd_4311923 : Nat := 2214089044176838315132333

theorem tailTrace_4311923 : CollatzResearch.WordTrace tailWord_4311923 prefixEnd_4311923 2214089044176838315132333 := by
  unfold tailWord_4311923
  simp only [CollatzResearch.WordTrace]
  refine ⟨157268751957646863664292423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104845834638431242442861615 157268751957646863664292423)
  ·
    refine ⟨235903127936470295496438635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157268751957646863664292423 235903127936470295496438635)
    ·
      refine ⟨353854691904705443244657953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235903127936470295496438635 353854691904705443244657953)
      ·
        refine ⟨265391018928529082433493465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353854691904705443244657953 265391018928529082433493465)
        ·
          refine ⟨199043264196396811825120099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265391018928529082433493465 199043264196396811825120099)
          ·
            refine ⟨298564896294595217737680149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199043264196396811825120099 298564896294595217737680149)
            ·
              refine ⟨13995229513809150831453757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 298564896294595217737680149 13995229513809150831453757)
              ·
                refine ⟨5248211067678431561795159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13995229513809150831453757 5248211067678431561795159)
                ·
                  refine ⟨7872316601517647342692739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248211067678431561795159 7872316601517647342692739)
                  ·
                    refine ⟨11808474902276471014039109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7872316601517647342692739 11808474902276471014039109)
                    ·
                      refine ⟨2214089044176838315132333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11808474902276471014039109 2214089044176838315132333)
                      ·
                        rfl

theorem cell23_4311923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_4311923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311923 prefixEnd_4311923 := by exact prefixLift 4311923
  have htrace : WordTrace (prefixWord ++ tailWord_4311923) baseStart_4311923 baseEnd_4311923 := by
    simpa [prefixWord, tailWord_4311923, baseEnd_4311923] using wordTrace_append hprefix tailTrace_4311923
  have hstable : (prefixWord ++ tailWord_4311923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311923).length < 2 ^ (prefixWord ++ tailWord_4311923).sum := by decide
  have hdescent : baseEnd_4311923 < baseStart_4311923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
