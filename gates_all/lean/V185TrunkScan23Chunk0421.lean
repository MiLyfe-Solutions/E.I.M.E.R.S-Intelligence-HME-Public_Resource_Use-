import V185TrunkScan23Chunk0420

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2489425 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 1, 4]
def baseStart_2489425 : Nat := 118140960795 + 2489425 * 2 ^ 59
def prefixEnd_2489425 : Nat := 4983230072969 + 3 ^ 40 * 2489425 * 2
def baseEnd_2489425 : Nat := 426090526106342615646283

theorem tailTrace_2489425 : CollatzResearch.WordTrace tailWord_2489425 prefixEnd_2489425 426090526106342615646283 := by
  unfold tailWord_2489425
  simp only [CollatzResearch.WordTrace]
  refine ⟨90796789006245859786397729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60531192670830573190931819 90796789006245859786397729)
  ·
    refine ⟨68097591754684394839798297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90796789006245859786397729 68097591754684394839798297)
    ·
      refine ⟨51073193816013296129848723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68097591754684394839798297 51073193816013296129848723)
      ·
        refine ⟨76609790724019944194773085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51073193816013296129848723 76609790724019944194773085)
        ·
          refine ⟨28728671521507479073039907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76609790724019944194773085 28728671521507479073039907)
          ·
            refine ⟨43093007282261218609559861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28728671521507479073039907 43093007282261218609559861)
            ·
              refine ⟨4039969432711989244646237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43093007282261218609559861 4039969432711989244646237)
              ·
                refine ⟨1514988537266995966742339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4039969432711989244646237 1514988537266995966742339)
                ·
                  refine ⟨2272482805900493950113509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514988537266995966742339 2272482805900493950113509)
                  ·
                    refine ⟨426090526106342615646283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272482805900493950113509 426090526106342615646283)
                    ·
                      rfl

theorem cell23_2489425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_2489425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489425 prefixEnd_2489425 := by exact prefixLift 2489425
  have htrace : WordTrace (prefixWord ++ tailWord_2489425) baseStart_2489425 baseEnd_2489425 := by
    simpa [prefixWord, tailWord_2489425, baseEnd_2489425] using wordTrace_append hprefix tailTrace_2489425
  have hstable : (prefixWord ++ tailWord_2489425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489425).length < 2 ^ (prefixWord ++ tailWord_2489425).sum := by decide
  have hdescent : baseEnd_2489425 < baseStart_2489425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489442 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2489442 : Nat := 118140960795 + 2489442 * 2 ^ 59
def prefixEnd_2489442 : Nat := 4983230072969 + 3 ^ 40 * 2489442 * 2
def baseEnd_2489442 : Nat := 426093435830051426808757

theorem tailTrace_2489442 : CollatzResearch.WordTrace tailWord_2489442 prefixEnd_2489442 426093435830051426808757 := by
  unfold tailWord_2489442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22699352261796067922441645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60531606031456181126511053 22699352261796067922441645)
  ·
    refine ⟨8512257098173525470915617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22699352261796067922441645 8512257098173525470915617)
    ·
      refine ⟨6384192823630144103186713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8512257098173525470915617 6384192823630144103186713)
      ·
        refine ⟨4788144617722608077390035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384192823630144103186713 4788144617722608077390035)
        ·
          refine ⟨7182216926583912116085053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788144617722608077390035 7182216926583912116085053)
          ·
            refine ⟨2693331347468967043531895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7182216926583912116085053 2693331347468967043531895)
            ·
              refine ⟨4039997021203450565297843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693331347468967043531895 4039997021203450565297843)
              ·
                refine ⟨6059995531805175847946765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039997021203450565297843 6059995531805175847946765)
                ·
                  refine ⟨2272498324426940942980037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6059995531805175847946765 2272498324426940942980037)
                  ·
                    refine ⟨426093435830051426808757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272498324426940942980037 426093435830051426808757)
                    ·
                      rfl

theorem cell23_2489442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2489442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489442 prefixEnd_2489442 := by exact prefixLift 2489442
  have htrace : WordTrace (prefixWord ++ tailWord_2489442) baseStart_2489442 baseEnd_2489442 := by
    simpa [prefixWord, tailWord_2489442, baseEnd_2489442] using wordTrace_append hprefix tailTrace_2489442
  have hstable : (prefixWord ++ tailWord_2489442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489442).length < 2 ^ (prefixWord ++ tailWord_2489442).sum := by decide
  have hdescent : baseEnd_2489442 < baseStart_2489442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489475 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 2, 3, 2]
def baseStart_2489475 : Nat := 118140960795 + 2489475 * 2 ^ 59
def prefixEnd_2489475 : Nat := 4983230072969 + 3 ^ 40 * 2489475 * 2
def baseEnd_2489475 : Nat := 1278297252351752651313619

theorem tailTrace_2489475 : CollatzResearch.WordTrace tailWord_2489475 prefixEnd_2489475 1278297252351752651313619 := by
  unfold tailWord_2489475
  simp only [CollatzResearch.WordTrace]
  refine ⟨90798612656064718325717879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60532408437376478883811919 90798612656064718325717879)
  ·
    refine ⟨136197918984097077488576819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90798612656064718325717879 136197918984097077488576819)
    ·
      refine ⟨204296878476145616232865229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136197918984097077488576819 204296878476145616232865229)
      ·
        refine ⟨76611329428554606087324461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204296878476145616232865229 76611329428554606087324461)
        ·
          refine ⟨28729248535707977282746673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76611329428554606087324461 28729248535707977282746673)
          ·
            refine ⟨21546936401780982962060005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28729248535707977282746673 21546936401780982962060005)
            ·
              refine ⟨4040050575333934305386251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21546936401780982962060005 4040050575333934305386251)
              ·
                refine ⟨6060075863000901458079377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040050575333934305386251 6060075863000901458079377)
                ·
                  refine ⟨4545056897250676093559533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6060075863000901458079377 4545056897250676093559533)
                  ·
                    refine ⟨1704396336469003535084825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4545056897250676093559533 1704396336469003535084825)
                    ·
                      refine ⟨1278297252351752651313619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704396336469003535084825 1278297252351752651313619)
                      ·
                        rfl

theorem cell23_2489475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_2489475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489475 prefixEnd_2489475 := by exact prefixLift 2489475
  have htrace : WordTrace (prefixWord ++ tailWord_2489475) baseStart_2489475 baseEnd_2489475 := by
    simpa [prefixWord, tailWord_2489475, baseEnd_2489475] using wordTrace_append hprefix tailTrace_2489475
  have hstable : (prefixWord ++ tailWord_2489475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489475).length < 2 ^ (prefixWord ++ tailWord_2489475).sum := by decide
  have hdescent : baseEnd_2489475 < baseStart_2489475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489481 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_2489481 : Nat := 118140960795 + 2489481 * 2 ^ 59
def prefixEnd_2489481 : Nat := 4983230072969 + 3 ^ 40 * 2489481 * 2
def baseEnd_2489481 : Nat := 426100111078559875946197

theorem tailTrace_2489481 : CollatzResearch.WordTrace tailWord_2489481 prefixEnd_2489481 426100111078559875946197 := by
  unfold tailWord_2489481
  simp only [CollatzResearch.WordTrace]
  refine ⟨90798831494042981350436297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60532554329361987566957531 90798831494042981350436297)
  ·
    refine ⟨68099123620532236012827223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90798831494042981350436297 68099123620532236012827223)
    ·
      refine ⟨102148685430798354019240835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68099123620532236012827223 102148685430798354019240835)
      ·
        refine ⟨153223028146197531028861253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102148685430798354019240835 153223028146197531028861253)
        ·
          refine ⟨28729317777412037067911485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153223028146197531028861253 28729317777412037067911485)
          ·
            refine ⟨10773494166529513900466807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28729317777412037067911485 10773494166529513900466807)
            ·
              refine ⟨16160241249794270850700211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10773494166529513900466807 16160241249794270850700211)
              ·
                refine ⟨24240361874691406276050317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16160241249794270850700211 24240361874691406276050317)
                ·
                  refine ⟨9090135703009277353518869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24240361874691406276050317 9090135703009277353518869)
                  ·
                    refine ⟨426100111078559875946197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9090135703009277353518869 426100111078559875946197)
                    ·
                      rfl

theorem cell23_2489481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_2489481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489481 prefixEnd_2489481 := by exact prefixLift 2489481
  have htrace : WordTrace (prefixWord ++ tailWord_2489481) baseStart_2489481 baseEnd_2489481 := by
    simpa [prefixWord, tailWord_2489481, baseEnd_2489481] using wordTrace_append hprefix tailTrace_2489481
  have hstable : (prefixWord ++ tailWord_2489481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489481).length < 2 ^ (prefixWord ++ tailWord_2489481).sum := by decide
  have hdescent : baseEnd_2489481 < baseStart_2489481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489482 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_2489482 : Nat := 118140960795 + 2489482 * 2 ^ 59
def prefixEnd_2489482 : Nat := 4983230072969 + 3 ^ 40 * 2489482 * 2
def baseEnd_2489482 : Nat := 1278300846716334123926087

theorem tailTrace_2489482 : CollatzResearch.WordTrace tailWord_2489482 prefixEnd_2489482 1278300846716334123926087 := by
  unfold tailWord_2489482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22699716991759839630305675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60532578644692905680815133 22699716991759839630305675)
  ·
    refine ⟨34049575487639759445458513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22699716991759839630305675 34049575487639759445458513)
    ·
      refine ⟨25537181615729819584093885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34049575487639759445458513 25537181615729819584093885)
      ·
        refine ⟨9576443105898682344035207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25537181615729819584093885 9576443105898682344035207)
        ·
          refine ⟨14364664658848023516052811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9576443105898682344035207 14364664658848023516052811)
          ·
            refine ⟨21546996988272035274079217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14364664658848023516052811 21546996988272035274079217)
            ·
              refine ⟨16160247741204026455559413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21546996988272035274079217 16160247741204026455559413)
              ·
                refine ⟨1515023225737877480208695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16160247741204026455559413 1515023225737877480208695)
                ·
                  refine ⟨2272534838606816220313043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515023225737877480208695 2272534838606816220313043)
                  ·
                    refine ⟨3408802257910224330469565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2272534838606816220313043 3408802257910224330469565)
                    ·
                      refine ⟨1278300846716334123926087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3408802257910224330469565 1278300846716334123926087)
                      ·
                        rfl

theorem cell23_2489482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_2489482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489482 prefixEnd_2489482 := by exact prefixLift 2489482
  have htrace : WordTrace (prefixWord ++ tailWord_2489482) baseStart_2489482 baseEnd_2489482 := by
    simpa [prefixWord, tailWord_2489482, baseEnd_2489482] using wordTrace_append hprefix tailTrace_2489482
  have hstable : (prefixWord ++ tailWord_2489482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489482).length < 2 ^ (prefixWord ++ tailWord_2489482).sum := by decide
  have hdescent : baseEnd_2489482 < baseStart_2489482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489522 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_2489522 : Nat := 118140960795 + 2489522 * 2 ^ 59
def prefixEnd_2489522 : Nat := 4983230072969 + 3 ^ 40 * 2489522 * 2
def baseEnd_2489522 : Nat := 1278321385942513967425903

theorem tailTrace_2489522 : CollatzResearch.WordTrace tailWord_2489522 prefixEnd_2489522 1278321385942513967425903 := by
  unfold tailWord_2489522
  simp only [CollatzResearch.WordTrace]
  refine ⟨22700081721723611338169705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60533551257929630235119213 22700081721723611338169705)
  ·
    refine ⟨17025061291292708503627279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22700081721723611338169705 17025061291292708503627279)
    ·
      refine ⟨25537591936939062755440919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17025061291292708503627279 25537591936939062755440919)
      ·
        refine ⟨38306387905408594133161379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25537591936939062755440919 38306387905408594133161379)
        ·
          refine ⟨57459581858112891199742069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38306387905408594133161379 57459581858112891199742069)
          ·
            refine ⟨5386835799198083549975819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57459581858112891199742069 5386835799198083549975819)
            ·
              refine ⟨8080253698797125324963729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386835799198083549975819 8080253698797125324963729)
              ·
                refine ⟨6060190274097843993722797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8080253698797125324963729 6060190274097843993722797)
                ·
                  refine ⟨2272571352786691497646049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6060190274097843993722797 2272571352786691497646049)
                  ·
                    refine ⟨1704428514590018623234537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272571352786691497646049 1704428514590018623234537)
                    ·
                      refine ⟨1278321385942513967425903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704428514590018623234537 1278321385942513967425903)
                      ·
                        rfl

theorem cell23_2489522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_2489522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489522 prefixEnd_2489522 := by exact prefixLift 2489522
  have htrace : WordTrace (prefixWord ++ tailWord_2489522) baseStart_2489522 baseEnd_2489522 := by
    simpa [prefixWord, tailWord_2489522, baseEnd_2489522] using wordTrace_append hprefix tailTrace_2489522
  have hstable : (prefixWord ++ tailWord_2489522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489522).length < 2 ^ (prefixWord ++ tailWord_2489522).sum := by decide
  have hdescent : baseEnd_2489522 < baseStart_2489522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489549 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2489549 : Nat := 118140960795 + 2489549 * 2 ^ 59
def prefixEnd_2489549 : Nat := 4983230072969 + 3 ^ 40 * 2489549 * 2
def baseEnd_2489549 : Nat := 426111749973395120596093

theorem tailTrace_2489549 : CollatzResearch.WordTrace tailWord_2489549 prefixEnd_2489549 426111749973395120596093 := by
  unfold tailWord_2489549
  simp only [CollatzResearch.WordTrace]
  refine ⟨90801311657796628963911701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60534207771864419309274467 90801311657796628963911701)
  ·
    refine ⟨4256311483959216982683361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90801311657796628963911701 4256311483959216982683361)
    ·
      refine ⟨3192233612969412737012521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4256311483959216982683361 3192233612969412737012521)
      ·
        refine ⟨2394175209727059552759391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3192233612969412737012521 2394175209727059552759391)
        ·
          refine ⟨3591262814590589329139087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394175209727059552759391 3591262814590589329139087)
          ·
            refine ⟨5386894221885883993708631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591262814590589329139087 5386894221885883993708631)
            ·
              refine ⟨8080341332828825990562947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386894221885883993708631 8080341332828825990562947)
              ·
                refine ⟨12120511999243238985844421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8080341332828825990562947 12120511999243238985844421)
                ·
                  refine ⟨2272595999858107309845829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12120511999243238985844421 2272595999858107309845829)
                  ·
                    refine ⟨426111749973395120596093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272595999858107309845829 426111749973395120596093)
                    ·
                      rfl

theorem cell23_2489549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2489549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489549 prefixEnd_2489549 := by exact prefixLift 2489549
  have htrace : WordTrace (prefixWord ++ tailWord_2489549) baseStart_2489549 baseEnd_2489549 := by
    simpa [prefixWord, tailWord_2489549, baseEnd_2489549] using wordTrace_append hprefix tailTrace_2489549
  have hstable : (prefixWord ++ tailWord_2489549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489549).length < 2 ^ (prefixWord ++ tailWord_2489549).sum := by decide
  have hdescent : baseEnd_2489549 < baseStart_2489549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489551 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_2489551 : Nat := 118140960795 + 2489551 * 2 ^ 59
def prefixEnd_2489551 : Nat := 4983230072969 + 3 ^ 40 * 2489551 * 2
def baseEnd_2489551 : Nat := 1278336276881494353963269

theorem tailTrace_2489551 : CollatzResearch.WordTrace tailWord_2489551 prefixEnd_2489551 1278336276881494353963269 := by
  unfold tailWord_2489551
  simp only [CollatzResearch.WordTrace]
  refine ⟨90801384603789383305484507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60534256402526255536989671 90801384603789383305484507)
  ·
    refine ⟨136202076905684074958226761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90801384603789383305484507 136202076905684074958226761)
    ·
      refine ⟨102151557679263056218670071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136202076905684074958226761 102151557679263056218670071)
      ·
        refine ⟨153227336518894584328005107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102151557679263056218670071 153227336518894584328005107)
        ·
          refine ⟨229841004778341876492007661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153227336518894584328005107 229841004778341876492007661)
          ·
            refine ⟨86190376791878203684502873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229841004778341876492007661 86190376791878203684502873)
            ·
              refine ⟨64642782593908652763377155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86190376791878203684502873 64642782593908652763377155)
              ·
                refine ⟨96964173890862979145065733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64642782593908652763377155 96964173890862979145065733)
                ·
                  refine ⟨18180782604536808589699825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96964173890862979145065733 18180782604536808589699825)
                  ·
                    refine ⟨13635586953402606442274869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18180782604536808589699825 13635586953402606442274869)
                    ·
                      refine ⟨1278336276881494353963269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13635586953402606442274869 1278336276881494353963269)
                      ·
                        rfl

theorem cell23_2489551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_2489551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489551 prefixEnd_2489551 := by exact prefixLift 2489551
  have htrace : WordTrace (prefixWord ++ tailWord_2489551) baseStart_2489551 baseEnd_2489551 := by
    simpa [prefixWord, tailWord_2489551, baseEnd_2489551] using wordTrace_append hprefix tailTrace_2489551
  have hstable : (prefixWord ++ tailWord_2489551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489551).length < 2 ^ (prefixWord ++ tailWord_2489551).sum := by decide
  have hdescent : baseEnd_2489551 < baseStart_2489551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489556 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2489556 : Nat := 118140960795 + 2489556 * 2 ^ 59
def prefixEnd_2489556 : Nat := 4983230072969 + 3 ^ 40 * 2489556 * 2
def baseEnd_2489556 : Nat := 1278338844284766834400747

theorem tailTrace_2489556 : CollatzResearch.WordTrace tailWord_2489556 prefixEnd_2489556 1278338844284766834400747 := by
  unfold tailWord_2489556
  simp only [CollatzResearch.WordTrace]
  refine ⟨45400783484385634579708261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60534377979180846106277681 45400783484385634579708261)
  ·
    refine ⟨8512646903322306483695299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45400783484385634579708261 8512646903322306483695299)
    ·
      refine ⟨12768970354983459725542949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8512646903322306483695299 12768970354983459725542949)
      ·
        refine ⟨2394181941559398698539303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12768970354983459725542949 2394181941559398698539303)
        ·
          refine ⟨3591272912339098047808955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394181941559398698539303 3591272912339098047808955)
          ·
            refine ⟨5386909368508647071713433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591272912339098047808955 5386909368508647071713433)
            ·
              refine ⟨4040182026381485303785075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386909368508647071713433 4040182026381485303785075)
              ·
                refine ⟨6060273039572227955677613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040182026381485303785075 6060273039572227955677613)
                ·
                  refine ⟨2272602389839585483379105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6060273039572227955677613 2272602389839585483379105)
                  ·
                    refine ⟨1704451792379689112534329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272602389839585483379105 1704451792379689112534329)
                    ·
                      refine ⟨1278338844284766834400747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704451792379689112534329 1278338844284766834400747)
                      ·
                        rfl

theorem cell23_2489556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2489556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489556 prefixEnd_2489556 := by exact prefixLift 2489556
  have htrace : WordTrace (prefixWord ++ tailWord_2489556) baseStart_2489556 baseEnd_2489556 := by
    simpa [prefixWord, tailWord_2489556, baseEnd_2489556] using wordTrace_append hprefix tailTrace_2489556
  have hstable : (prefixWord ++ tailWord_2489556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489556).length < 2 ^ (prefixWord ++ tailWord_2489556).sum := by decide
  have hdescent : baseEnd_2489556 < baseStart_2489556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489582 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_2489582 : Nat := 118140960795 + 2489582 * 2 ^ 59
def prefixEnd_2489582 : Nat := 4983230072969 + 3 ^ 40 * 2489582 * 2
def baseEnd_2489582 : Nat := 1278352194781783732675627

theorem tailTrace_2489582 : CollatzResearch.WordTrace tailWord_2489582 prefixEnd_2489582 1278352194781783732675627 := by
  unfold tailWord_2489582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11350314408334634449982875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60535010177784717066575333 11350314408334634449982875)
  ·
    refine ⟨17025471612501951674974313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11350314408334634449982875 17025471612501951674974313)
    ·
      refine ⟨12769103709376463756230735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17025471612501951674974313 12769103709376463756230735)
      ·
        refine ⟨19153655564064695634346103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12769103709376463756230735 19153655564064695634346103)
        ·
          refine ⟨28730483346097043451519155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19153655564064695634346103 28730483346097043451519155)
          ·
            refine ⟨43095725019145565177278733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28730483346097043451519155 43095725019145565177278733)
            ·
              refine ⟨16160896882179586941479525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43095725019145565177278733 16160896882179586941479525)
              ·
                refine ⟨3030168165408672551527411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16160896882179586941479525 3030168165408672551527411)
                ·
                  refine ⟨4545252248113008827291117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3030168165408672551527411 4545252248113008827291117)
                  ·
                    refine ⟨1704469593042378310234169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4545252248113008827291117 1704469593042378310234169)
                    ·
                      refine ⟨1278352194781783732675627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704469593042378310234169 1278352194781783732675627)
                      ·
                        rfl

theorem cell23_2489582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_2489582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489582 prefixEnd_2489582 := by exact prefixLift 2489582
  have htrace : WordTrace (prefixWord ++ tailWord_2489582) baseStart_2489582 baseEnd_2489582 := by
    simpa [prefixWord, tailWord_2489582, baseEnd_2489582] using wordTrace_append hprefix tailTrace_2489582
  have hstable : (prefixWord ++ tailWord_2489582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489582).length < 2 ^ (prefixWord ++ tailWord_2489582).sum := by decide
  have hdescent : baseEnd_2489582 < baseStart_2489582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489612 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_2489612 : Nat := 118140960795 + 2489612 * 2 ^ 59
def prefixEnd_2489612 : Nat := 4983230072969 + 3 ^ 40 * 2489612 * 2
def baseEnd_2489612 : Nat := 1278367599201418615300489

theorem tailTrace_2489612 : CollatzResearch.WordTrace tailWord_2489612 prefixEnd_2489612 1278367599201418615300489 := by
  unfold tailWord_2489612
  simp only [CollatzResearch.WordTrace]
  refine ⟨45401804728284195361727545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60535739637712260482303393 45401804728284195361727545)
  ·
    refine ⟨34051353546213146521295659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45401804728284195361727545 34051353546213146521295659)
    ·
      refine ⟨51077030319319719781943489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34051353546213146521295659 51077030319319719781943489)
      ·
        refine ⟨38307772739489789836457617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51077030319319719781943489 38307772739489789836457617)
        ·
          refine ⟨28730829554617342377343213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38307772739489789836457617 28730829554617342377343213)
          ·
            refine ⟨10774061082981503391503705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28730829554617342377343213 10774061082981503391503705)
            ·
              refine ⟨8080545812236127543627779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10774061082981503391503705 8080545812236127543627779)
              ·
                refine ⟨12120818718354191315441669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8080545812236127543627779 12120818718354191315441669)
                ·
                  refine ⟨2272653509691410871645313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12120818718354191315441669 2272653509691410871645313)
                  ·
                    refine ⟨1704490132268558153733985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272653509691410871645313 1704490132268558153733985)
                    ·
                      refine ⟨1278367599201418615300489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704490132268558153733985 1278367599201418615300489)
                      ·
                        rfl

theorem cell23_2489612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_2489612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489612 prefixEnd_2489612 := by exact prefixLift 2489612
  have htrace : WordTrace (prefixWord ++ tailWord_2489612) baseStart_2489612 baseEnd_2489612 := by
    simpa [prefixWord, tailWord_2489612, baseEnd_2489612] using wordTrace_append hprefix tailTrace_2489612
  have hstable : (prefixWord ++ tailWord_2489612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489612).length < 2 ^ (prefixWord ++ tailWord_2489612).sum := by decide
  have hdescent : baseEnd_2489612 < baseStart_2489612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489652 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 5]
def baseStart_2489652 : Nat := 118140960795 + 2489652 * 2 ^ 59
def prefixEnd_2489652 : Nat := 4983230072969 + 3 ^ 40 * 2489652 * 2
def baseEnd_2489652 : Nat := 142043126491955384311145

theorem tailTrace_2489652 : CollatzResearch.WordTrace tailWord_2489652 prefixEnd_2489652 142043126491955384311145 := by
  unfold tailWord_2489652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45402534188211738777455605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60536712250948985036607473 45402534188211738777455605)
  ·
    refine ⟨4256487580144850510386463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45402534188211738777455605 4256487580144850510386463)
    ·
      refine ⟨6384731370217275765579695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4256487580144850510386463 6384731370217275765579695)
      ·
        refine ⟨9577097055325913648369543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6384731370217275765579695 9577097055325913648369543)
        ·
          refine ⟨14365645582988870472554315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9577097055325913648369543 14365645582988870472554315)
          ·
            refine ⟨21548468374483305708831473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14365645582988870472554315 21548468374483305708831473)
            ·
              refine ⟨16161351280862479281623605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21548468374483305708831473 16161351280862479281623605)
              ·
                refine ⟨1515126682580857432652213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16161351280862479281623605 1515126682580857432652213)
                ·
                  refine ⟨142043126491955384311145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1515126682580857432652213 142043126491955384311145)
                  ·
                    rfl

theorem cell23_2489652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_2489652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489652 prefixEnd_2489652 := by exact prefixLift 2489652
  have htrace : WordTrace (prefixWord ++ tailWord_2489652) baseStart_2489652 baseEnd_2489652 := by
    simpa [prefixWord, tailWord_2489652, baseEnd_2489652] using wordTrace_append hprefix tailTrace_2489652
  have hstable : (prefixWord ++ tailWord_2489652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489652).length < 2 ^ (prefixWord ++ tailWord_2489652).sum := by decide
  have hdescent : baseEnd_2489652 < baseStart_2489652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489658 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_2489658 : Nat := 118140960795 + 2489658 * 2 ^ 59
def prefixEnd_2489658 : Nat := 4983230072969 + 3 ^ 40 * 2489658 * 2
def baseEnd_2489658 : Nat := 1278391219311525435325277

theorem tailTrace_2489658 : CollatzResearch.WordTrace tailWord_2489658 prefixEnd_2489658 1278391219311525435325277 := by
  unfold tailWord_2489658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22701321803600435144907407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60536858142934493719753085 22701321803600435144907407)
  ·
    refine ⟨34051982705400652717361111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22701321803600435144907407 34051982705400652717361111)
    ·
      refine ⟨51077974058100979076041667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34051982705400652717361111 51077974058100979076041667)
      ·
        refine ⟨76616961087151468614062501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51077974058100979076041667 76616961087151468614062501)
        ·
          refine ⟨14365680203840900365136719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76616961087151468614062501 14365680203840900365136719)
          ·
            refine ⟨21548520305761350547705079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14365680203840900365136719 21548520305761350547705079)
            ·
              refine ⟨32322780458642025821557619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21548520305761350547705079 32322780458642025821557619)
              ·
                refine ⟨48484170687963038732336429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32322780458642025821557619 48484170687963038732336429)
                ·
                  refine ⟨18181564007986139524626161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48484170687963038732336429 18181564007986139524626161)
                  ·
                    refine ⟨13636173005989604643469621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18181564007986139524626161 13636173005989604643469621)
                    ·
                      refine ⟨1278391219311525435325277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13636173005989604643469621 1278391219311525435325277)
                      ·
                        rfl

theorem cell23_2489658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_2489658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489658 prefixEnd_2489658 := by exact prefixLift 2489658
  have htrace : WordTrace (prefixWord ++ tailWord_2489658) baseStart_2489658 baseEnd_2489658 := by
    simpa [prefixWord, tailWord_2489658, baseEnd_2489658] using wordTrace_append hprefix tailTrace_2489658
  have hstable : (prefixWord ++ tailWord_2489658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489658).length < 2 ^ (prefixWord ++ tailWord_2489658).sum := by decide
  have hdescent : baseEnd_2489658 < baseStart_2489658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489686 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2489686 : Nat := 118140960795 + 2489686 * 2 ^ 59
def prefixEnd_2489686 : Nat := 4983230072969 + 3 ^ 40 * 2489686 * 2
def baseEnd_2489686 : Nat := 142045066307761258419461

theorem tailTrace_2489686 : CollatzResearch.WordTrace tailWord_2489686 prefixEnd_2489686 142045066307761258419461 := by
  unfold tailWord_2489686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675394278643768835103057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60537538972200200907765941 5675394278643768835103057)
  ·
    refine ⟨4256545708982826626327293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5675394278643768835103057 4256545708982826626327293)
    ·
      refine ⟨1596204640868559984872735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4256545708982826626327293 1596204640868559984872735)
      ·
        refine ⟨2394306961302839977309103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596204640868559984872735 2394306961302839977309103)
        ·
          refine ⟨3591460441954259965963655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394306961302839977309103 3591460441954259965963655)
          ·
            refine ⟨5387190662931389948945483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591460441954259965963655 5387190662931389948945483)
            ·
              refine ⟨8080785994397084923418225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387190662931389948945483 8080785994397084923418225)
              ·
                refine ⟨6060589495797813692563669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8080785994397084923418225 6060589495797813692563669)
                ·
                  refine ⟨142045066307761258419461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6060589495797813692563669 142045066307761258419461)
                  ·
                    rfl

theorem cell23_2489686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2489686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489686 prefixEnd_2489686 := by exact prefixLift 2489686
  have htrace : WordTrace (prefixWord ++ tailWord_2489686) baseStart_2489686 baseEnd_2489686 := by
    simpa [prefixWord, tailWord_2489686, baseEnd_2489686] using wordTrace_append hprefix tailTrace_2489686
  have hstable : (prefixWord ++ tailWord_2489686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489686).length < 2 ^ (prefixWord ++ tailWord_2489686).sum := by decide
  have hdescent : baseEnd_2489686 < baseStart_2489686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489705 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_2489705 : Nat := 118140960795 + 2489705 * 2 ^ 59
def prefixEnd_2489705 : Nat := 4983230072969 + 3 ^ 40 * 2489705 * 2
def baseEnd_2489705 : Nat := 1278415352902286751437561

theorem tailTrace_2489705 : CollatzResearch.WordTrace tailWord_2489705 prefixEnd_2489705 1278415352902286751437561 := by
  unfold tailWord_2489705
  simp only [CollatzResearch.WordTrace]
  refine ⟨90807001445231467606590569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60538000963487645071060379 90807001445231467606590569)
  ·
    refine ⟨68105251083923600704942927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90807001445231467606590569 68105251083923600704942927)
    ·
      refine ⟨102157876625885401057414391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68105251083923600704942927 102157876625885401057414391)
      ·
        refine ⟨153236814938828101586121587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102157876625885401057414391 153236814938828101586121587)
        ·
          refine ⟨229855222408242152379182381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153236814938828101586121587 229855222408242152379182381)
          ·
            refine ⟨86195708403090807142193393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229855222408242152379182381 86195708403090807142193393)
            ·
              refine ⟨64646781302318105356645045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86195708403090807142193393 64646781302318105356645045)
              ·
                refine ⟨6060635747092322377185473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64646781302318105356645045 6060635747092322377185473)
                ·
                  refine ⟨4545476810319241782889105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6060635747092322377185473 4545476810319241782889105)
                  ·
                    refine ⟨3409107607739431337166829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4545476810319241782889105 3409107607739431337166829)
                    ·
                      refine ⟨1278415352902286751437561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409107607739431337166829 1278415352902286751437561)
                      ·
                        rfl

theorem cell23_2489705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_2489705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489705 prefixEnd_2489705 := by exact prefixLift 2489705
  have htrace : WordTrace (prefixWord ++ tailWord_2489705) baseStart_2489705 baseEnd_2489705 := by
    simpa [prefixWord, tailWord_2489705, baseEnd_2489705] using wordTrace_append hprefix tailTrace_2489705
  have hstable : (prefixWord ++ tailWord_2489705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489705).length < 2 ^ (prefixWord ++ tailWord_2489705).sum := by decide
  have hdescent : baseEnd_2489705 < baseStart_2489705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489729 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2489729 : Nat := 118140960795 + 2489729 * 2 ^ 59
def prefixEnd_2489729 : Nat := 4983230072969 + 3 ^ 40 * 2489729 * 2
def baseEnd_2489729 : Nat := 426142558812664885845817

theorem tailTrace_2489729 : CollatzResearch.WordTrace tailWord_2489729 prefixEnd_2489729 426142558812664885845817 := by
  unfold tailWord_2489729
  simp only [CollatzResearch.WordTrace]
  refine ⟨90807876797144519705464241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60538584531429679803642827 90807876797144519705464241)
  ·
    refine ⟨68105907597858389779098181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90807876797144519705464241 68105907597858389779098181)
    ·
      refine ⟨12769857674598448083580909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68105907597858389779098181 12769857674598448083580909)
      ·
        refine ⟨4788696627974418031342841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12769857674598448083580909 4788696627974418031342841)
        ·
          refine ⟨3591522470980813523507131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4788696627974418031342841 3591522470980813523507131)
          ·
            refine ⟨5387283706471220285260697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591522470980813523507131 5387283706471220285260697)
            ·
              refine ⟨4040462779853415213945523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5387283706471220285260697 4040462779853415213945523)
              ·
                refine ⟨6060694169780122820918285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040462779853415213945523 6060694169780122820918285)
                ·
                  refine ⟨2272760313667546057844357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6060694169780122820918285 2272760313667546057844357)
                  ·
                    refine ⟨426142558812664885845817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272760313667546057844357 426142558812664885845817)
                    ·
                      rfl

theorem cell23_2489729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2489729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489729 prefixEnd_2489729 := by exact prefixLift 2489729
  have htrace : WordTrace (prefixWord ++ tailWord_2489729) baseStart_2489729 baseEnd_2489729 := by
    simpa [prefixWord, tailWord_2489729, baseEnd_2489729] using wordTrace_append hprefix tailTrace_2489729
  have hstable : (prefixWord ++ tailWord_2489729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489729).length < 2 ^ (prefixWord ++ tailWord_2489729).sum := by decide
  have hdescent : baseEnd_2489729 < baseStart_2489729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489795 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5]
def baseStart_2489795 : Nat := 118140960795 + 2489795 * 2 ^ 59
def prefixEnd_2489795 : Nat := 4983230072969 + 3 ^ 40 * 2489795 * 2
def baseEnd_2489795 : Nat := 1278461566161191399312147

theorem tailTrace_2489795 : CollatzResearch.WordTrace tailWord_2489795 prefixEnd_2489795 1278461566161191399312147 := by
  unfold tailWord_2489795
  simp only [CollatzResearch.WordTrace]
  refine ⟨90810284014905412977366839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60540189343270275318244559 90810284014905412977366839)
  ·
    refine ⟨136215426022358119466050259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90810284014905412977366839 136215426022358119466050259)
    ·
      refine ⟨204323139033537179199075389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136215426022358119466050259 204323139033537179199075389)
      ·
        refine ⟨76621177137576442199653271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204323139033537179199075389 76621177137576442199653271)
        ·
          refine ⟨114931765706364663299479907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76621177137576442199653271 114931765706364663299479907)
          ·
            refine ⟨172397648559546994949219861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114931765706364663299479907 172397648559546994949219861)
            ·
              refine ⟨8081139776228765388244681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172397648559546994949219861 8081139776228765388244681)
              ·
                refine ⟨6060854832171574041183511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8081139776228765388244681 6060854832171574041183511)
                ·
                  refine ⟨9091282248257361061775267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060854832171574041183511 9091282248257361061775267)
                  ·
                    refine ⟨13636923372386041592662901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9091282248257361061775267 13636923372386041592662901)
                    ·
                      refine ⟨1278461566161191399312147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13636923372386041592662901 1278461566161191399312147)
                      ·
                        rfl

theorem cell23_2489795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_2489795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489795 prefixEnd_2489795 := by exact prefixLift 2489795
  have htrace : WordTrace (prefixWord ++ tailWord_2489795) baseStart_2489795 baseEnd_2489795 := by
    simpa [prefixWord, tailWord_2489795, baseEnd_2489795] using wordTrace_append hprefix tailTrace_2489795
  have hstable : (prefixWord ++ tailWord_2489795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489795).length < 2 ^ (prefixWord ++ tailWord_2489795).sum := by decide
  have hdescent : baseEnd_2489795 < baseStart_2489795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489829 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2489829 : Nat := 118140960795 + 2489829 * 2 ^ 59
def prefixEnd_2489829 : Nat := 4983230072969 + 3 ^ 40 * 2489829 * 2
def baseEnd_2489829 : Nat := 1278479024503444266286991

theorem tailTrace_2489829 : CollatzResearch.WordTrace tailWord_2489829 prefixEnd_2489829 1278479024503444266286991 := by
  unfold tailWord_2489829
  simp only [CollatzResearch.WordTrace]
  refine ⟨90811524096782236784104541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60541016064521491189403027 90811524096782236784104541)
  ·
    refine ⟨34054321536293338794039203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90811524096782236784104541 34054321536293338794039203)
    ·
      refine ⟨51081482304440008191058805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34054321536293338794039203 51081482304440008191058805)
      ·
        refine ⟨4788888966041250767911763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51081482304440008191058805 4788888966041250767911763)
        ·
          refine ⟨7183333449061876151867645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788888966041250767911763 7183333449061876151867645)
          ·
            refine ⟨2693750043398203556950367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7183333449061876151867645 2693750043398203556950367)
            ·
              refine ⟨4040625065097305335425551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693750043398203556950367 4040625065097305335425551)
              ·
                refine ⟨6060937597645958003138327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040625065097305335425551 6060937597645958003138327)
                ·
                  refine ⟨9091406396468937004707491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6060937597645958003138327 9091406396468937004707491)
                  ·
                    refine ⟨13637109594703405507061237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9091406396468937004707491 13637109594703405507061237)
                    ·
                      refine ⟨1278479024503444266286991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13637109594703405507061237 1278479024503444266286991)
                      ·
                        rfl

theorem cell23_2489829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2489829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489829 prefixEnd_2489829 := by exact prefixLift 2489829
  have htrace : WordTrace (prefixWord ++ tailWord_2489829) baseStart_2489829 baseEnd_2489829 := by
    simpa [prefixWord, tailWord_2489829, baseEnd_2489829] using wordTrace_append hprefix tailTrace_2489829
  have hstable : (prefixWord ++ tailWord_2489829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489829).length < 2 ^ (prefixWord ++ tailWord_2489829).sum := by decide
  have hdescent : baseEnd_2489829 < baseStart_2489829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489837 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2489837 : Nat := 118140960795 + 2489837 * 2 ^ 59
def prefixEnd_2489837 : Nat := 4983230072969 + 3 ^ 40 * 2489837 * 2
def baseEnd_2489837 : Nat := 1278483132348680234986955

theorem tailTrace_2489837 : CollatzResearch.WordTrace tailWord_2489837 prefixEnd_2489837 1278483132348680234986955 := by
  unfold tailWord_2489837
  simp only [CollatzResearch.WordTrace]
  refine ⟨90811815880753254150395765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60541210587168836100263843 90811815880753254150395765)
  ·
    refine ⟨8513607738820617576599603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90811815880753254150395765 8513607738820617576599603)
    ·
      refine ⟨12770411608230926364899405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513607738820617576599603 12770411608230926364899405)
      ·
        refine ⟨4788904353086597386837277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12770411608230926364899405 4788904353086597386837277)
        ·
          refine ⟨1795839132407474020063979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4788904353086597386837277 1795839132407474020063979)
          ·
            refine ⟨2693758698611211030095969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795839132407474020063979 2693758698611211030095969)
            ·
              refine ⟨2020319023958408272571977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693758698611211030095969 2020319023958408272571977)
              ·
                refine ⟨1515239267968806204428983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020319023958408272571977 1515239267968806204428983)
                ·
                  refine ⟨2272858901953209306643475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515239267968806204428983 2272858901953209306643475)
                  ·
                    refine ⟨3409288352929813959965213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2272858901953209306643475 3409288352929813959965213)
                    ·
                      refine ⟨1278483132348680234986955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409288352929813959965213 1278483132348680234986955)
                      ·
                        rfl

theorem cell23_2489837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2489837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489837 prefixEnd_2489837 := by exact prefixLift 2489837
  have htrace : WordTrace (prefixWord ++ tailWord_2489837) baseStart_2489837 baseEnd_2489837 := by
    simpa [prefixWord, tailWord_2489837, baseEnd_2489837] using wordTrace_append hprefix tailTrace_2489837
  have hstable : (prefixWord ++ tailWord_2489837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489837).length < 2 ^ (prefixWord ++ tailWord_2489837).sum := by decide
  have hdescent : baseEnd_2489837 < baseStart_2489837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489865 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_2489865 : Nat := 118140960795 + 2489865 * 2 ^ 59
def prefixEnd_2489865 : Nat := 4983230072969 + 3 ^ 40 * 2489865 * 2
def baseEnd_2489865 : Nat := 1278497509807006125436825

theorem tailTrace_2489865 : CollatzResearch.WordTrace tailWord_2489865 prefixEnd_2489865 1278497509807006125436825 := by
  unfold tailWord_2489865
  simp only [CollatzResearch.WordTrace]
  refine ⟨90812837124651814932415049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60541891416434543288276699 90812837124651814932415049)
  ·
    refine ⟨68109627843488861199311287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90812837124651814932415049 68109627843488861199311287)
    ·
      refine ⟨102164441765233291798966931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68109627843488861199311287 102164441765233291798966931)
      ·
        refine ⟨153246662647849937698450397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102164441765233291798966931 153246662647849937698450397)
        ·
          refine ⟨57467498492943726636918899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153246662647849937698450397 57467498492943726636918899)
          ·
            refine ⟨86201247739415589955378349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57467498492943726636918899 86201247739415589955378349)
            ·
              refine ⟨32325467902280846233266881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86201247739415589955378349 32325467902280846233266881)
              ·
                refine ⟨24244100926710634674950161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32325467902280846233266881 24244100926710634674950161)
                ·
                  refine ⟨18183075695032976006212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24244100926710634674950161 18183075695032976006212621)
                  ·
                    refine ⟨6818653385637366002329733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18183075695032976006212621 6818653385637366002329733)
                    ·
                      refine ⟨1278497509807006125436825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6818653385637366002329733 1278497509807006125436825)
                      ·
                        rfl

theorem cell23_2489865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_2489865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489865 prefixEnd_2489865 := by exact prefixLift 2489865
  have htrace : WordTrace (prefixWord ++ tailWord_2489865) baseStart_2489865 baseEnd_2489865 := by
    simpa [prefixWord, tailWord_2489865, baseEnd_2489865] using wordTrace_append hprefix tailTrace_2489865
  have hstable : (prefixWord ++ tailWord_2489865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489865).length < 2 ^ (prefixWord ++ tailWord_2489865).sum := by decide
  have hdescent : baseEnd_2489865 < baseStart_2489865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489910 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2489910 : Nat := 118140960795 + 2489910 * 2 ^ 59
def prefixEnd_2489910 : Nat := 4983230072969 + 3 ^ 40 * 2489910 * 2
def baseEnd_2489910 : Nat := 1278520616436458449374119

theorem tailTrace_2489910 : CollatzResearch.WordTrace tailWord_2489910 prefixEnd_2489910 1278520616436458449374119 := by
  unfold tailWord_2489910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675904900593049226112699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60542985606325858411868789 5675904900593049226112699)
  ·
    refine ⟨8513857350889573839169049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675904900593049226112699 8513857350889573839169049)
    ·
      refine ⟨6385393013167180379376787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8513857350889573839169049 6385393013167180379376787)
      ·
        refine ⟨9578089519750770569065181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6385393013167180379376787 9578089519750770569065181)
        ·
          refine ⟨3591783569906538963399443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9578089519750770569065181 3591783569906538963399443)
          ·
            refine ⟨5387675354859808445099165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591783569906538963399443 5387675354859808445099165)
            ·
              refine ⟨2020378258072428166912187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5387675354859808445099165 2020378258072428166912187)
              ·
                refine ⟨3030567387108642250368281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020378258072428166912187 3030567387108642250368281)
                ·
                  refine ⟨2272925540331481687776211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3030567387108642250368281 2272925540331481687776211)
                  ·
                    refine ⟨3409388310497222531664317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2272925540331481687776211 3409388310497222531664317)
                    ·
                      refine ⟨1278520616436458449374119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409388310497222531664317 1278520616436458449374119)
                      ·
                        rfl

theorem cell23_2489910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2489910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489910 prefixEnd_2489910 := by exact prefixLift 2489910
  have htrace : WordTrace (prefixWord ++ tailWord_2489910) baseStart_2489910 baseEnd_2489910 := by
    simpa [prefixWord, tailWord_2489910, baseEnd_2489910] using wordTrace_append hprefix tailTrace_2489910
  have hstable : (prefixWord ++ tailWord_2489910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489910).length < 2 ^ (prefixWord ++ tailWord_2489910).sum := by decide
  have hdescent : baseEnd_2489910 < baseStart_2489910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489912 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2489912 : Nat := 118140960795 + 2489912 * 2 ^ 59
def prefixEnd_2489912 : Nat := 4983230072969 + 3 ^ 40 * 2489912 * 2
def baseEnd_2489912 : Nat := 1278521643397767441549109

theorem tailTrace_2489912 : CollatzResearch.WordTrace tailWord_2489912 prefixEnd_2489912 1278521643397767441549109 := by
  unfold tailWord_2489912
  simp only [CollatzResearch.WordTrace]
  refine ⟨45407275677740770979687995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60543034236987694639583993 45407275677740770979687995)
  ·
    refine ⟨68110913516611156469531993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45407275677740770979687995 68110913516611156469531993)
    ·
      refine ⟨51083185137458367352148995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68110913516611156469531993 51083185137458367352148995)
      ·
        refine ⟨76624777706187551028223493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51083185137458367352148995 76624777706187551028223493)
        ·
          refine ⟨14367145819910165817791905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76624777706187551028223493 14367145819910165817791905)
          ·
            refine ⟨10775359364932624363343929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14367145819910165817791905 10775359364932624363343929)
            ·
              refine ⟨8081519523699468272507947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10775359364932624363343929 8081519523699468272507947)
              ·
                refine ⟨12122279285549202408761921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081519523699468272507947 12122279285549202408761921)
                ·
                  refine ⟨9091709464161901806571441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12122279285549202408761921 9091709464161901806571441)
                  ·
                    refine ⟨6818782098121426354928581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9091709464161901806571441 6818782098121426354928581)
                    ·
                      refine ⟨1278521643397767441549109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6818782098121426354928581 1278521643397767441549109)
                      ·
                        rfl

theorem cell23_2489912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2489912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489912 prefixEnd_2489912 := by exact prefixLift 2489912
  have htrace : WordTrace (prefixWord ++ tailWord_2489912) baseStart_2489912 baseEnd_2489912 := by
    simpa [prefixWord, tailWord_2489912, baseEnd_2489912] using wordTrace_append hprefix tailTrace_2489912
  have hstable : (prefixWord ++ tailWord_2489912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489912).length < 2 ^ (prefixWord ++ tailWord_2489912).sum := by decide
  have hdescent : baseEnd_2489912 < baseStart_2489912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489945 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_2489945 : Nat := 118140960795 + 2489945 * 2 ^ 59
def prefixEnd_2489945 : Nat := 4983230072969 + 3 ^ 40 * 2489945 * 2
def baseEnd_2489945 : Nat := 1278538588259365812436457

theorem tailTrace_2489945 : CollatzResearch.WordTrace tailWord_2489945 prefixEnd_2489945 1278538588259365812436457 := by
  unfold tailWord_2489945
  simp only [CollatzResearch.WordTrace]
  refine ⟨90815754964361988595327289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60543836642907992396884859 90815754964361988595327289)
  ·
    refine ⟨68111816223271491446495467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90815754964361988595327289 68111816223271491446495467)
    ·
      refine ⟨102167724334907237169743201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68111816223271491446495467 102167724334907237169743201)
      ·
        refine ⟨76625793251180427877307401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102167724334907237169743201 76625793251180427877307401)
        ·
          refine ⟨57469344938385320907980551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76625793251180427877307401 57469344938385320907980551)
          ·
            refine ⟨86204017407577981361970827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57469344938385320907980551 86204017407577981361970827)
            ·
              refine ⟨129306026111366972042956241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86204017407577981361970827 129306026111366972042956241)
              ·
                refine ⟨96979519583525229032217181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129306026111366972042956241 96979519583525229032217181)
                ·
                  refine ⟨36367319843821960887081443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96979519583525229032217181 36367319843821960887081443)
                  ·
                    refine ⟨54550979765732941330622165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36367319843821960887081443 54550979765732941330622165)
                    ·
                      refine ⟨1278538588259365812436457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54550979765732941330622165 1278538588259365812436457)
                      ·
                        rfl

theorem cell23_2489945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_2489945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489945 prefixEnd_2489945 := by exact prefixLift 2489945
  have htrace : WordTrace (prefixWord ++ tailWord_2489945) baseStart_2489945 baseEnd_2489945 := by
    simpa [prefixWord, tailWord_2489945, baseEnd_2489945] using wordTrace_append hprefix tailTrace_2489945
  have hstable : (prefixWord ++ tailWord_2489945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489945).length < 2 ^ (prefixWord ++ tailWord_2489945).sum := by decide
  have hdescent : baseEnd_2489945 < baseStart_2489945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489956 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 5]
def baseStart_2489956 : Nat := 118140960795 + 2489956 * 2 ^ 59
def prefixEnd_2489956 : Nat := 4983230072969 + 3 ^ 40 * 2489956 * 2
def baseEnd_2489956 : Nat := 142060470727396141044323

theorem tailTrace_2489956 : CollatzResearch.WordTrace tailWord_2489956 prefixEnd_2489956 142060470727396141044323 := by
  unfold tailWord_2489956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45408078083661068736988861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60544104111548091649318481 45408078083661068736988861)
  ·
    refine ⟨17028029281372900776370823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45408078083661068736988861 17028029281372900776370823)
    ·
      refine ⟨25542043922059351164556235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17028029281372900776370823 25542043922059351164556235)
      ·
        refine ⟨38313065883089026746834353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25542043922059351164556235 38313065883089026746834353)
        ·
          refine ⟨28734799412316770060125765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38313065883089026746834353 28734799412316770060125765)
          ·
            refine ⟨5387774889809394386273581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28734799412316770060125765 5387774889809394386273581)
            ·
              refine ⟨2020415583678522894852593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5387774889809394386273581 2020415583678522894852593)
              ·
                refine ⟨1515311687758892171139445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020415583678522894852593 1515311687758892171139445)
                ·
                  refine ⟨142060470727396141044323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1515311687758892171139445 142060470727396141044323)
                  ·
                    rfl

theorem cell23_2489956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_2489956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489956 prefixEnd_2489956 := by exact prefixLift 2489956
  have htrace : WordTrace (prefixWord ++ tailWord_2489956) baseStart_2489956 baseEnd_2489956 := by
    simpa [prefixWord, tailWord_2489956, baseEnd_2489956] using wordTrace_append hprefix tailTrace_2489956
  have hstable : (prefixWord ++ tailWord_2489956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489956).length < 2 ^ (prefixWord ++ tailWord_2489956).sum := by decide
  have hdescent : baseEnd_2489956 < baseStart_2489956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489962 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2489962 : Nat := 118140960795 + 2489962 * 2 ^ 59
def prefixEnd_2489962 : Nat := 4983230072969 + 3 ^ 40 * 2489962 * 2
def baseEnd_2489962 : Nat := 1278547317430492245923879

theorem tailTrace_2489962 : CollatzResearch.WordTrace tailWord_2489962 prefixEnd_2489962 1278547317430492245923879 := by
  unfold tailWord_2489962
  simp only [CollatzResearch.WordTrace]
  refine ⟨22704093751325100124674035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60544250003533600332464093 22704093751325100124674035)
  ·
    refine ⟨34056140626987650187011053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22704093751325100124674035 34056140626987650187011053)
    ·
      refine ⟨12771052735120368820129145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34056140626987650187011053 12771052735120368820129145)
      ·
        refine ⟨9578289551340276615096859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12771052735120368820129145 9578289551340276615096859)
        ·
          refine ⟨14367434327010414922645289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578289551340276615096859 14367434327010414922645289)
          ·
            refine ⟨10775575745257811191983967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14367434327010414922645289 10775575745257811191983967)
            ·
              refine ⟨16163363617886716787975951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10775575745257811191983967 16163363617886716787975951)
              ·
                refine ⟨24245045426830075181963927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16163363617886716787975951 24245045426830075181963927)
                ·
                  refine ⟨36367568140245112772945891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24245045426830075181963927 36367568140245112772945891)
                  ·
                    refine ⟨54551352210367669159418837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36367568140245112772945891 54551352210367669159418837)
                    ·
                      refine ⟨1278547317430492245923879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54551352210367669159418837 1278547317430492245923879)
                      ·
                        rfl

theorem cell23_2489962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2489962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489962 prefixEnd_2489962 := by exact prefixLift 2489962
  have htrace : WordTrace (prefixWord ++ tailWord_2489962) baseStart_2489962 baseEnd_2489962 := by
    simpa [prefixWord, tailWord_2489962, baseEnd_2489962] using wordTrace_append hprefix tailTrace_2489962
  have hstable : (prefixWord ++ tailWord_2489962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489962).length < 2 ^ (prefixWord ++ tailWord_2489962).sum := by decide
  have hdescent : baseEnd_2489962 < baseStart_2489962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489989 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_2489989 : Nat := 118140960795 + 2489989 * 2 ^ 59
def prefixEnd_2489989 : Nat := 4983230072969 + 3 ^ 40 * 2489989 * 2
def baseEnd_2489989 : Nat := 1278561181408163640286255

theorem tailTrace_2489989 : CollatzResearch.WordTrace tailWord_2489989 prefixEnd_2489989 1278561181408163640286255 := by
  unfold tailWord_2489989
  simp only [CollatzResearch.WordTrace]
  refine ⟨90817359776202584109929021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60544906517468389406619347 90817359776202584109929021)
  ·
    refine ⟨34056509916075969041223383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90817359776202584109929021 34056509916075969041223383)
    ·
      refine ⟨51084764874113953561835075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34056509916075969041223383 51084764874113953561835075)
      ·
        refine ⟨76627147311170930342752613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51084764874113953561835075 76627147311170930342752613)
        ·
          refine ⟨14367590120844549439266115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76627147311170930342752613 14367590120844549439266115)
          ·
            refine ⟨21551385181266824158899173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14367590120844549439266115 21551385181266824158899173)
            ·
              refine ⟨4040884721487529529793595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21551385181266824158899173 4040884721487529529793595)
              ·
                refine ⟨6061327082231294294690393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040884721487529529793595 6061327082231294294690393)
                ·
                  refine ⟨4545995311673470721017795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6061327082231294294690393 4545995311673470721017795)
                  ·
                    refine ⟨6818992967510206081526693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4545995311673470721017795 6818992967510206081526693)
                    ·
                      refine ⟨1278561181408163640286255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6818992967510206081526693 1278561181408163640286255)
                      ·
                        rfl

theorem cell23_2489989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_2489989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489989 prefixEnd_2489989 := by exact prefixLift 2489989
  have htrace : WordTrace (prefixWord ++ tailWord_2489989) baseStart_2489989 baseEnd_2489989 := by
    simpa [prefixWord, tailWord_2489989, baseEnd_2489989] using wordTrace_append hprefix tailTrace_2489989
  have hstable : (prefixWord ++ tailWord_2489989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489989).length < 2 ^ (prefixWord ++ tailWord_2489989).sum := by decide
  have hdescent : baseEnd_2489989 < baseStart_2489989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490029 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 6]
def baseStart_2490029 : Nat := 118140960795 + 2490029 * 2 ^ 59
def prefixEnd_2490029 : Nat := 4983230072969 + 3 ^ 40 * 2490029 * 2
def baseEnd_2490029 : Nat := 142064635626038164865119

theorem tailTrace_2490029 : CollatzResearch.WordTrace tailWord_2490029 prefixEnd_2490029 142064635626038164865119 := by
  unfold tailWord_2490029
  simp only [CollatzResearch.WordTrace]
  refine ⟨90818818696057670941385141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60545879130705113960923427 90818818696057670941385141)
  ·
    refine ⟨8514264252755406650754857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90818818696057670941385141 8514264252755406650754857)
    ·
      refine ⟨6385698189566554988066143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8514264252755406650754857 6385698189566554988066143)
      ·
        refine ⟨9578547284349832482099215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6385698189566554988066143 9578547284349832482099215)
        ·
          refine ⟨14367820926524748723148823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578547284349832482099215 14367820926524748723148823)
          ·
            refine ⟨21551731389787123084723235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14367820926524748723148823 21551731389787123084723235)
            ·
              refine ⟨32327597084680684627084853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21551731389787123084723235 32327597084680684627084853)
              ·
                refine ⟨3030712226688814183789205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32327597084680684627084853 3030712226688814183789205)
                ·
                  refine ⟨142064635626038164865119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3030712226688814183789205 142064635626038164865119)
                  ·
                    rfl

theorem cell23_2490029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_2490029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490029 prefixEnd_2490029 := by exact prefixLift 2490029
  have htrace : WordTrace (prefixWord ++ tailWord_2490029) baseStart_2490029 baseEnd_2490029 := by
    simpa [prefixWord, tailWord_2490029, baseEnd_2490029] using wordTrace_append hprefix tailTrace_2490029
  have hstable : (prefixWord ++ tailWord_2490029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490029).length < 2 ^ (prefixWord ++ tailWord_2490029).sum := by decide
  have hdescent : baseEnd_2490029 < baseStart_2490029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490073 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 1, 1, 3]
def baseStart_2490073 : Nat := 118140960795 + 2490073 * 2 ^ 59
def prefixEnd_2490073 : Nat := 4983230072969 + 3 ^ 40 * 2490073 * 2
def baseEnd_2490073 : Nat := 1278604313783141311635869

theorem tailTrace_2490073 : CollatzResearch.WordTrace tailWord_2490073 prefixEnd_2490073 1278604313783141311635869 := by
  unfold tailWord_2490073
  simp only [CollatzResearch.WordTrace]
  refine ⟨90820423507898266455986873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60546949005265510970657915 90820423507898266455986873)
  ·
    refine ⟨68115317630923699841990155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90820423507898266455986873 68115317630923699841990155)
    ·
      refine ⟨102172976446385549762985233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68115317630923699841990155 102172976446385549762985233)
      ·
        refine ⟨76629732334789162322238925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102172976446385549762985233 76629732334789162322238925)
        ·
          refine ⟨28736149625545935870839597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76629732334789162322238925 28736149625545935870839597)
          ·
            refine ⟨10776056109579725951564849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28736149625545935870839597 10776056109579725951564849)
            ·
              refine ⟨8082042082184794463673637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10776056109579725951564849 8082042082184794463673637)
              ·
                refine ⟨1515382890409648961938807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8082042082184794463673637 1515382890409648961938807)
                ·
                  refine ⟨2273074335614473442908211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515382890409648961938807 2273074335614473442908211)
                  ·
                    refine ⟨3409611503421710164362317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2273074335614473442908211 3409611503421710164362317)
                    ·
                      refine ⟨1278604313783141311635869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409611503421710164362317 1278604313783141311635869)
                      ·
                        rfl

theorem cell23_2490073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_2490073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490073 prefixEnd_2490073 := by exact prefixLift 2490073
  have htrace : WordTrace (prefixWord ++ tailWord_2490073) baseStart_2490073 baseEnd_2490073 := by
    simpa [prefixWord, tailWord_2490073, baseEnd_2490073] using wordTrace_append hprefix tailTrace_2490073
  have hstable : (prefixWord ++ tailWord_2490073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490073).length < 2 ^ (prefixWord ++ tailWord_2490073).sum := by decide
  have hdescent : baseEnd_2490073 < baseStart_2490073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490096 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2]
def baseStart_2490096 : Nat := 118140960795 + 2490096 * 2 ^ 59
def prefixEnd_2490096 : Nat := 4983230072969 + 3 ^ 40 * 2490096 * 2
def baseEnd_2490096 : Nat := 1278616123838194721648263

theorem tailTrace_2490096 : CollatzResearch.WordTrace tailWord_2490096 prefixEnd_2490096 1278616123838194721648263 := by
  unfold tailWord_2490096
  simp only [CollatzResearch.WordTrace]
  refine ⟨45410631193407470692037071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60547508257876627589382761 45410631193407470692037071)
  ·
    refine ⟨68115946790111206038055607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45410631193407470692037071 68115946790111206038055607)
    ·
      refine ⟨102173920185166809057083411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68115946790111206038055607 102173920185166809057083411)
      ·
        refine ⟨153260880277750213585625117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102173920185166809057083411 153260880277750213585625117)
        ·
          refine ⟨57472830104156330094609419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153260880277750213585625117 57472830104156330094609419)
          ·
            refine ⟨86209245156234495141914129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57472830104156330094609419 86209245156234495141914129)
            ·
              refine ⟨64656933867175871356435597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86209245156234495141914129 64656933867175871356435597)
              ·
                refine ⟨24246350200190951758663349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64656933867175871356435597 24246350200190951758663349)
                ·
                  refine ⟨2273095331267901727374689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24246350200190951758663349 2273095331267901727374689)
                  ·
                    refine ⟨1704821498450926295531017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2273095331267901727374689 1704821498450926295531017)
                    ·
                      refine ⟨1278616123838194721648263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704821498450926295531017 1278616123838194721648263)
                      ·
                        rfl

theorem cell23_2490096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 2, 2].length) (baseStart_2490096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490096 prefixEnd_2490096 := by exact prefixLift 2490096
  have htrace : WordTrace (prefixWord ++ tailWord_2490096) baseStart_2490096 baseEnd_2490096 := by
    simpa [prefixWord, tailWord_2490096, baseEnd_2490096] using wordTrace_append hprefix tailTrace_2490096
  have hstable : (prefixWord ++ tailWord_2490096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490096).length < 2 ^ (prefixWord ++ tailWord_2490096).sum := by decide
  have hdescent : baseEnd_2490096 < baseStart_2490096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490099 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3]
def baseStart_2490099 : Nat := 118140960795 + 2490099 * 2 ^ 59
def prefixEnd_2490099 : Nat := 4983230072969 + 3 ^ 40 * 2490099 * 2
def baseEnd_2490099 : Nat := 1278617664280158209910749

theorem tailTrace_2490099 : CollatzResearch.WordTrace tailWord_2490099 prefixEnd_2490099 1278617664280158209910749 := by
  unfold tailWord_2490099
  simp only [CollatzResearch.WordTrace]
  refine ⟨90821371805804072896433351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60547581203869381930955567 90821371805804072896433351)
  ·
    refine ⟨136232057708706109344650027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90821371805804072896433351 136232057708706109344650027)
    ·
      refine ⟨204348086563059164016975041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136232057708706109344650027 204348086563059164016975041)
      ·
        refine ⟨153261064922294373012731281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204348086563059164016975041 153261064922294373012731281)
        ·
          refine ⟨114945798691720779759548461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153261064922294373012731281 114945798691720779759548461)
          ·
            refine ⟨43104674509395292409830673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114945798691720779759548461 43104674509395292409830673)
            ·
              refine ⟨32328505882046469307373005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43104674509395292409830673 32328505882046469307373005)
              ·
                refine ⟨12123189705767425990264877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32328505882046469307373005 12123189705767425990264877)
                ·
                  refine ⟨4546196139662784746349329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12123189705767425990264877 4546196139662784746349329)
                  ·
                    refine ⟨3409647104747088559761997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546196139662784746349329 3409647104747088559761997)
                    ·
                      refine ⟨1278617664280158209910749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409647104747088559761997 1278617664280158209910749)
                      ·
                        rfl

theorem cell23_2490099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_2490099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490099 prefixEnd_2490099 := by exact prefixLift 2490099
  have htrace : WordTrace (prefixWord ++ tailWord_2490099) baseStart_2490099 baseEnd_2490099 := by
    simpa [prefixWord, tailWord_2490099, baseEnd_2490099] using wordTrace_append hprefix tailTrace_2490099
  have hstable : (prefixWord ++ tailWord_2490099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490099).length < 2 ^ (prefixWord ++ tailWord_2490099).sum := by decide
  have hdescent : baseEnd_2490099 < baseStart_2490099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490100 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2490100 : Nat := 118140960795 + 2490100 * 2 ^ 59
def prefixEnd_2490100 : Nat := 4983230072969 + 3 ^ 40 * 2490100 * 2
def baseEnd_2490100 : Nat := 1278618177760812705998245

theorem tailTrace_2490100 : CollatzResearch.WordTrace tailWord_2490100 prefixEnd_2490100 1278618177760812705998245 := by
  unfold tailWord_2490100
  simp only [CollatzResearch.WordTrace]
  refine ⟨45410704139400225033609877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60547605519200300044813169 45410704139400225033609877)
  ·
    refine ⟨2128626756534385548450463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45410704139400225033609877 2128626756534385548450463)
    ·
      refine ⟨3192940134801578322675695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128626756534385548450463 3192940134801578322675695)
      ·
        refine ⟨4789410202202367484013543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192940134801578322675695 4789410202202367484013543)
        ·
          refine ⟨7184115303303551226020315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789410202202367484013543 7184115303303551226020315)
          ·
            refine ⟨10776172954955326839030473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7184115303303551226020315 10776172954955326839030473)
            ·
              refine ⟨8082129716216495129272855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10776172954955326839030473 8082129716216495129272855)
              ·
                refine ⟨12123194574324742693909283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082129716216495129272855 12123194574324742693909283)
                ·
                  refine ⟨18184791861487114040863925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12123194574324742693909283 18184791861487114040863925)
                  ·
                    refine ⟨1704824237014416941330993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18184791861487114040863925 1704824237014416941330993)
                    ·
                      refine ⟨1278618177760812705998245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704824237014416941330993 1278618177760812705998245)
                      ·
                        rfl

theorem cell23_2490100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2490100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490100 prefixEnd_2490100 := by exact prefixLift 2490100
  have htrace : WordTrace (prefixWord ++ tailWord_2490100) baseStart_2490100 baseEnd_2490100 := by
    simpa [prefixWord, tailWord_2490100, baseEnd_2490100] using wordTrace_append hprefix tailTrace_2490100
  have hstable : (prefixWord ++ tailWord_2490100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490100).length < 2 ^ (prefixWord ++ tailWord_2490100).sum := by decide
  have hdescent : baseEnd_2490100 < baseStart_2490100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490116 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2490116 : Nat := 118140960795 + 2490116 * 2 ^ 59
def prefixEnd_2490116 : Nat := 4983230072969 + 3 ^ 40 * 2490116 * 2
def baseEnd_2490116 : Nat := 1278626393451284643398171

theorem tailTrace_2490116 : CollatzResearch.WordTrace tailWord_2490116 prefixEnd_2490116 1278626393451284643398171 := by
  unfold tailWord_2490116
  simp only [CollatzResearch.WordTrace]
  refine ⟨45410995923371242399901101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60547994564494989866534801 45410995923371242399901101)
  ·
    refine ⟨17029123471264215899962913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45410995923371242399901101 17029123471264215899962913)
    ·
      refine ⟨12771842603448161924972185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17029123471264215899962913 12771842603448161924972185)
      ·
        refine ⟨9578881952586121443729139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12771842603448161924972185 9578881952586121443729139)
        ·
          refine ⟨14368322928879182165593709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9578881952586121443729139 14368322928879182165593709)
          ·
            refine ⟨5388121098329693312097641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14368322928879182165593709 5388121098329693312097641)
            ·
              refine ⟨4041090823747269984073231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388121098329693312097641 4041090823747269984073231)
              ·
                refine ⟨6061636235620904976109847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041090823747269984073231 6061636235620904976109847)
                ·
                  refine ⟨9092454353431357464164771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061636235620904976109847 9092454353431357464164771)
                  ·
                    refine ⟨13638681530147036196247157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9092454353431357464164771 13638681530147036196247157)
                    ·
                      refine ⟨1278626393451284643398171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13638681530147036196247157 1278626393451284643398171)
                      ·
                        rfl

theorem cell23_2490116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2490116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490116 prefixEnd_2490116 := by exact prefixLift 2490116
  have htrace : WordTrace (prefixWord ++ tailWord_2490116) baseStart_2490116 baseEnd_2490116 := by
    simpa [prefixWord, tailWord_2490116, baseEnd_2490116] using wordTrace_append hprefix tailTrace_2490116
  have hstable : (prefixWord ++ tailWord_2490116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490116).length < 2 ^ (prefixWord ++ tailWord_2490116).sum := by decide
  have hdescent : baseEnd_2490116 < baseStart_2490116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490118 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2490118 : Nat := 118140960795 + 2490118 * 2 ^ 59
def prefixEnd_2490118 : Nat := 4983230072969 + 3 ^ 40 * 2490118 * 2
def baseEnd_2490118 : Nat := 426209140137531211857721

theorem tailTrace_2490118 : CollatzResearch.WordTrace tailWord_2490118 prefixEnd_2490118 426209140137531211857721 := by
  unfold tailWord_2490118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838189524772976223167969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60548043195156826094250005 2838189524772976223167969)
  ·
    refine ⟨2128642143579732167375977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2838189524772976223167969 2128642143579732167375977)
    ·
      refine ⟨1596481607684799125531983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2128642143579732167375977 1596481607684799125531983)
      ·
        refine ⟨2394722411527198688297975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596481607684799125531983 2394722411527198688297975)
        ·
          refine ⟨3592083617290798032446963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394722411527198688297975 3592083617290798032446963)
          ·
            refine ⟨5388125425936197048670445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592083617290798032446963 5388125425936197048670445)
            ·
              refine ⟨2020547034726073893251417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5388125425936197048670445 2020547034726073893251417)
              ·
                refine ⟨1515410276044555419938563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020547034726073893251417 1515410276044555419938563)
                ·
                  refine ⟨2273115414066833129907845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515410276044555419938563 2273115414066833129907845)
                  ·
                    refine ⟨426209140137531211857721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2273115414066833129907845 426209140137531211857721)
                    ·
                      rfl

theorem cell23_2490118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2490118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490118 prefixEnd_2490118 := by exact prefixLift 2490118
  have htrace : WordTrace (prefixWord ++ tailWord_2490118) baseStart_2490118 baseEnd_2490118 := by
    simpa [prefixWord, tailWord_2490118, baseEnd_2490118] using wordTrace_append hprefix tailTrace_2490118
  have hstable : (prefixWord ++ tailWord_2490118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490118).length < 2 ^ (prefixWord ++ tailWord_2490118).sum := by decide
  have hdescent : baseEnd_2490118 < baseStart_2490118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490146 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_2490146 : Nat := 118140960795 + 2490146 * 2 ^ 59
def prefixEnd_2490146 : Nat := 4983230072969 + 3 ^ 40 * 2490146 * 2
def baseEnd_2490146 : Nat := 1278641797870919526023033

theorem tailTrace_2490146 : CollatzResearch.WordTrace tailWord_2490146 prefixEnd_2490146 1278641797870919526023033 := by
  unfold tailWord_2490146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22705771509158449980848573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60548724024422533282262861 22705771509158449980848573)
  ·
    refine ⟨8514664315934418742818215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22705771509158449980848573 8514664315934418742818215)
    ·
      refine ⟨12771996473901628114227323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8514664315934418742818215 12771996473901628114227323)
      ·
        refine ⟨19157994710852442171340985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12771996473901628114227323 19157994710852442171340985)
        ·
          refine ⟨14368496033139331628505739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19157994710852442171340985 14368496033139331628505739)
          ·
            refine ⟨21552744049708997442758609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14368496033139331628505739 21552744049708997442758609)
            ·
              refine ⟨16164558037281748082068957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21552744049708997442758609 16164558037281748082068957)
              ·
                refine ⟨6061709263980655530775859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16164558037281748082068957 6061709263980655530775859)
                ·
                  refine ⟨9092563895970983296163789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061709263980655530775859 9092563895970983296163789)
                  ·
                    refine ⟨3409711460989118736061421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9092563895970983296163789 3409711460989118736061421)
                    ·
                      refine ⟨1278641797870919526023033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409711460989118736061421 1278641797870919526023033)
                      ·
                        rfl

theorem cell23_2490146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_2490146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490146 prefixEnd_2490146 := by exact prefixLift 2490146
  have htrace : WordTrace (prefixWord ++ tailWord_2490146) baseStart_2490146 baseEnd_2490146 := by
    simpa [prefixWord, tailWord_2490146, baseEnd_2490146] using wordTrace_append hprefix tailTrace_2490146
  have hstable : (prefixWord ++ tailWord_2490146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490146).length < 2 ^ (prefixWord ++ tailWord_2490146).sum := by decide
  have hdescent : baseEnd_2490146 < baseStart_2490146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490186 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_2490186 : Nat := 118140960795 + 2490186 * 2 ^ 59
def prefixEnd_2490186 : Nat := 4983230072969 + 3 ^ 40 * 2490186 * 2
def baseEnd_2490186 : Nat := 1278662337097099369522849

theorem tailTrace_2490186 : CollatzResearch.WordTrace tailWord_2490186 prefixEnd_2490186 1278662337097099369522849 := by
  unfold tailWord_2490186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22706136239122221688712603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60549696637659257836566941 22706136239122221688712603)
  ·
    refine ⟨34059204358683332533068905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22706136239122221688712603 34059204358683332533068905)
    ·
      refine ⟨25544403269012499399801679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34059204358683332533068905 25544403269012499399801679)
      ·
        refine ⟨38316604903518749099702519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25544403269012499399801679 38316604903518749099702519)
        ·
          refine ⟨57474907355278123649553779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38316604903518749099702519 57474907355278123649553779)
          ·
            refine ⟨86212361032917185474330669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57474907355278123649553779 86212361032917185474330669)
            ·
              refine ⟨32329635387343944552874001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86212361032917185474330669 32329635387343944552874001)
              ·
                refine ⟨24247226540507958414655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32329635387343944552874001 24247226540507958414655501)
                ·
                  refine ⟨9092709952690484405495813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24247226540507958414655501 9092709952690484405495813)
                  ·
                    refine ⟨1704883116129465826030465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9092709952690484405495813 1704883116129465826030465)
                    ·
                      refine ⟨1278662337097099369522849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704883116129465826030465 1278662337097099369522849)
                      ·
                        rfl

theorem cell23_2490186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_2490186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490186 prefixEnd_2490186 := by exact prefixLift 2490186
  have htrace : WordTrace (prefixWord ++ tailWord_2490186) baseStart_2490186 baseEnd_2490186 := by
    simpa [prefixWord, tailWord_2490186, baseEnd_2490186] using wordTrace_append hprefix tailTrace_2490186
  have hstable : (prefixWord ++ tailWord_2490186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490186).length < 2 ^ (prefixWord ++ tailWord_2490186).sum := by decide
  have hdescent : baseEnd_2490186 < baseStart_2490186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490196 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_2490196 : Nat := 118140960795 + 2490196 * 2 ^ 59
def prefixEnd_2490196 : Nat := 4983230072969 + 3 ^ 40 * 2490196 * 2
def baseEnd_2490196 : Nat := 426222490634548110132601

theorem tailTrace_2490196 : CollatzResearch.WordTrace tailWord_2490196 prefixEnd_2490196 426222490634548110132601 := by
  unfold tailWord_2490196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45412454843226329231357221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60549939790968438975142961 45412454843226329231357221)
  ·
    refine ⟨8514835283104936730879479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45412454843226329231357221 8514835283104936730879479)
    ·
      refine ⟨12772252924657405096319219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8514835283104936730879479 12772252924657405096319219)
      ·
        refine ⟨19158379386986107644478829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12772252924657405096319219 19158379386986107644478829)
        ·
          refine ⟨7184392270119790366679561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19158379386986107644478829 7184392270119790366679561)
          ·
            refine ⟨5388294202589842775009671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7184392270119790366679561 5388294202589842775009671)
            ·
              refine ⟨8082441303884764162514507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388294202589842775009671 8082441303884764162514507)
              ·
                refine ⟨12123661955827146243771761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082441303884764162514507 12123661955827146243771761)
                ·
                  refine ⟨9092746466870359682828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12123661955827146243771761 9092746466870359682828821)
                  ·
                    refine ⟨426222490634548110132601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9092746466870359682828821 426222490634548110132601)
                    ·
                      rfl

theorem cell23_2490196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_2490196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490196 prefixEnd_2490196 := by exact prefixLift 2490196
  have htrace : WordTrace (prefixWord ++ tailWord_2490196) baseStart_2490196 baseEnd_2490196 := by
    simpa [prefixWord, tailWord_2490196, baseEnd_2490196] using wordTrace_append hprefix tailTrace_2490196
  have hstable : (prefixWord ++ tailWord_2490196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490196).length < 2 ^ (prefixWord ++ tailWord_2490196).sum := by decide
  have hdescent : baseEnd_2490196 < baseStart_2490196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490209 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 7]
def baseStart_2490209 : Nat := 118140960795 + 2490209 * 2 ^ 59
def prefixEnd_2490209 : Nat := 4983230072969 + 3 ^ 40 * 2490209 * 2
def baseEnd_2490209 : Nat := 142074905239128086615027

theorem tailTrace_2490209 : CollatzResearch.WordTrace tailWord_2490209 prefixEnd_2490209 142074905239128086615027 := by
  unfold tailWord_2490209
  simp only [CollatzResearch.WordTrace]
  refine ⟨90825383835405561682937681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60550255890270374455291787 90825383835405561682937681)
  ·
    refine ⟨68119037876554171262203261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90825383835405561682937681 68119037876554171262203261)
    ·
      refine ⟨25544639203707814223326223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68119037876554171262203261 25544639203707814223326223)
      ·
        refine ⟨38316958805561721334989335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25544639203707814223326223 38316958805561721334989335)
        ·
          refine ⟨57475438208342582002484003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38316958805561721334989335 57475438208342582002484003)
          ·
            refine ⟨86213157312513873003726005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57475438208342582002484003 86213157312513873003726005)
            ·
              refine ⟨8082483498048175594099313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86213157312513873003726005 8082483498048175594099313)
              ·
                refine ⟨6061862623536131695574485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8082483498048175594099313 6061862623536131695574485)
                ·
                  refine ⟨142074905239128086615027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6061862623536131695574485 142074905239128086615027)
                  ·
                    rfl

theorem cell23_2490209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_2490209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490209 prefixEnd_2490209 := by exact prefixLift 2490209
  have htrace : WordTrace (prefixWord ++ tailWord_2490209) baseStart_2490209 baseEnd_2490209 := by
    simpa [prefixWord, tailWord_2490209, baseEnd_2490209] using wordTrace_append hprefix tailTrace_2490209
  have hstable : (prefixWord ++ tailWord_2490209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490209).length < 2 ^ (prefixWord ++ tailWord_2490209).sum := by decide
  have hdescent : baseEnd_2490209 < baseStart_2490209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490219 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3]
def baseStart_2490219 : Nat := 118140960795 + 2490219 * 2 ^ 59
def prefixEnd_2490219 : Nat := 4983230072969 + 3 ^ 40 * 2490219 * 2
def baseEnd_2490219 : Nat := 1278679281958697740410197

theorem tailTrace_2490219 : CollatzResearch.WordTrace tailWord_2490219 prefixEnd_2490219 1278679281958697740410197 := by
  unfold tailWord_2490219
  simp only [CollatzResearch.WordTrace]
  refine ⟨90825748565369333390801711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60550499043579555593867807 90825748565369333390801711)
  ·
    refine ⟨136238622848054000086202567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90825748565369333390801711 136238622848054000086202567)
    ·
      refine ⟨204357934272081000129303851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136238622848054000086202567 204357934272081000129303851)
      ·
        refine ⟨306536901408121500193955777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204357934272081000129303851 306536901408121500193955777)
        ·
          refine ⟨229902676056091125145466833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306536901408121500193955777 229902676056091125145466833)
          ·
            refine ⟨172427007042068343859100125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229902676056091125145466833 172427007042068343859100125)
            ·
              refine ⟨64660127640775628947162547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172427007042068343859100125 64660127640775628947162547)
              ·
                refine ⟨96990191461163443420743821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64660127640775628947162547 96990191461163443420743821)
                ·
                  refine ⟨36371321797936291282778933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96990191461163443420743821 36371321797936291282778933)
                  ·
                    refine ⟨3409811418556527307760525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36371321797936291282778933 3409811418556527307760525)
                    ·
                      refine ⟨1278679281958697740410197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409811418556527307760525 1278679281958697740410197)
                      ·
                        rfl

theorem cell23_2490219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3].length) (baseStart_2490219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490219 prefixEnd_2490219 := by exact prefixLift 2490219
  have htrace : WordTrace (prefixWord ++ tailWord_2490219) baseStart_2490219 baseEnd_2490219 := by
    simpa [prefixWord, tailWord_2490219, baseEnd_2490219] using wordTrace_append hprefix tailTrace_2490219
  have hstable : (prefixWord ++ tailWord_2490219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490219).length < 2 ^ (prefixWord ++ tailWord_2490219).sum := by decide
  have hdescent : baseEnd_2490219 < baseStart_2490219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490239 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 4, 5]
def baseStart_2490239 : Nat := 118140960795 + 2490239 * 2 ^ 59
def prefixEnd_2490239 : Nat := 4983230072969 + 3 ^ 40 * 2490239 * 2
def baseEnd_2490239 : Nat := 426229850523929220720035

theorem tailTrace_2490239 : CollatzResearch.WordTrace tailWord_2490239 prefixEnd_2490239 426229850523929220720035 := by
  unfold tailWord_2490239
  simp only [CollatzResearch.WordTrace]
  refine ⟨90826478025296876806529771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60550985350197917871019847 90826478025296876806529771)
  ·
    refine ⟨136239717037945315209794657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90826478025296876806529771 136239717037945315209794657)
    ·
      refine ⟨102179787778458986407345993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136239717037945315209794657 102179787778458986407345993)
      ·
        refine ⟨76634840833844239805509495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102179787778458986407345993 76634840833844239805509495)
        ·
          refine ⟨114952261250766359708264243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76634840833844239805509495 114952261250766359708264243)
          ·
            refine ⟨172428391876149539562396365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114952261250766359708264243 172428391876149539562396365)
            ·
              refine ⟨64660646953556077335898637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172428391876149539562396365 64660646953556077335898637)
              ·
                refine ⟨24247742607583529000961989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64660646953556077335898637 24247742607583529000961989)
                ·
                  refine ⟨4546451738921911687680373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24247742607583529000961989 4546451738921911687680373)
                  ·
                    refine ⟨426229850523929220720035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4546451738921911687680373 426229850523929220720035)
                    ·
                      rfl

theorem cell23_2490239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_2490239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490239 prefixEnd_2490239 := by exact prefixLift 2490239
  have htrace : WordTrace (prefixWord ++ tailWord_2490239) baseStart_2490239 baseEnd_2490239 := by
    simpa [prefixWord, tailWord_2490239, baseEnd_2490239] using wordTrace_append hprefix tailTrace_2490239
  have hstable : (prefixWord ++ tailWord_2490239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490239).length < 2 ^ (prefixWord ++ tailWord_2490239).sum := by decide
  have hdescent : baseEnd_2490239 < baseStart_2490239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490249 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_2490249 : Nat := 118140960795 + 2490249 * 2 ^ 59
def prefixEnd_2490249 : Nat := 4983230072969 + 3 ^ 40 * 2490249 * 2
def baseEnd_2490249 : Nat := 1278694686378332623035059

theorem tailTrace_2490249 : CollatzResearch.WordTrace tailWord_2490249 prefixEnd_2490249 1278694686378332623035059 := by
  unfold tailWord_2490249
  simp only [CollatzResearch.WordTrace]
  refine ⟨90826842755260648514393801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60551228503507099009595867 90826842755260648514393801)
  ·
    refine ⟨68120132066445486385795351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90826842755260648514393801 68120132066445486385795351)
    ·
      refine ⟨102180198099668229578693027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68120132066445486385795351 102180198099668229578693027)
      ·
        refine ⟨153270297149502344368039541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102180198099668229578693027 153270297149502344368039541)
        ·
          refine ⟨14369090357765844784503707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153270297149502344368039541 14369090357765844784503707)
          ·
            refine ⟨21553635536648767176755561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14369090357765844784503707 21553635536648767176755561)
            ·
              refine ⟨16165226652486575382566671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21553635536648767176755561 16165226652486575382566671)
              ·
                refine ⟨24247839978729863073850007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16165226652486575382566671 24247839978729863073850007)
                ·
                  refine ⟨36371759968094794610775011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24247839978729863073850007 36371759968094794610775011)
                  ·
                    refine ⟨54557639952142191916162517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36371759968094794610775011 54557639952142191916162517)
                    ·
                      refine ⟨1278694686378332623035059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54557639952142191916162517 1278694686378332623035059)
                      ·
                        rfl

theorem cell23_2490249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_2490249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490249 prefixEnd_2490249 := by exact prefixLift 2490249
  have htrace : WordTrace (prefixWord ++ tailWord_2490249) baseStart_2490249 baseEnd_2490249 := by
    simpa [prefixWord, tailWord_2490249, baseEnd_2490249] using wordTrace_append hprefix tailTrace_2490249
  have hstable : (prefixWord ++ tailWord_2490249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490249).length < 2 ^ (prefixWord ++ tailWord_2490249).sum := by decide
  have hdescent : baseEnd_2490249 < baseStart_2490249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490254 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2490254 : Nat := 118140960795 + 2490254 * 2 ^ 59
def prefixEnd_2490254 : Nat := 4983230072969 + 3 ^ 40 * 2490254 * 2
def baseEnd_2490254 : Nat := 1278697253781605103472537

theorem tailTrace_2490254 : CollatzResearch.WordTrace tailWord_2490254 prefixEnd_2490254 1278697253781605103472537 := by
  unfold tailWord_2490254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353378140030316796040727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60551350080161689578883877 11353378140030316796040727)
  ·
    refine ⟨17030067210045475194061091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11353378140030316796040727 17030067210045475194061091)
    ·
      refine ⟨25545100815068212791091637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17030067210045475194061091 25545100815068212791091637)
      ·
        refine ⟨2394853201412644949164841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25545100815068212791091637 2394853201412644949164841)
        ·
          refine ⟨1796139901059483711873631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2394853201412644949164841 1796139901059483711873631)
          ·
            refine ⟨2694209851589225567810447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796139901059483711873631 2694209851589225567810447)
            ·
              refine ⟨4041314777383838351715671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2694209851589225567810447 4041314777383838351715671)
              ·
                refine ⟨6061972166075757527573507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041314777383838351715671 6061972166075757527573507)
                ·
                  refine ⟨9092958249113636291360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6061972166075757527573507 9092958249113636291360261)
                  ·
                    refine ⟨1704929671708806804630049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9092958249113636291360261 1704929671708806804630049)
                    ·
                      refine ⟨1278697253781605103472537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704929671708806804630049 1278697253781605103472537)
                      ·
                        rfl

theorem cell23_2490254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2490254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490254 prefixEnd_2490254 := by exact prefixLift 2490254
  have htrace : WordTrace (prefixWord ++ tailWord_2490254) baseStart_2490254 baseEnd_2490254 := by
    simpa [prefixWord, tailWord_2490254, baseEnd_2490254] using wordTrace_append hprefix tailTrace_2490254
  have hstable : (prefixWord ++ tailWord_2490254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490254).length < 2 ^ (prefixWord ++ tailWord_2490254).sum := by decide
  have hdescent : baseEnd_2490254 < baseStart_2490254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490276 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2490276 : Nat := 118140960795 + 2490276 * 2 ^ 59
def prefixEnd_2490276 : Nat := 4983230072969 + 3 ^ 40 * 2490276 * 2
def baseEnd_2490276 : Nat := 1278708550356004017397435

theorem tailTrace_2490276 : CollatzResearch.WordTrace tailWord_2490276 prefixEnd_2490276 1278708550356004017397435 := by
  unfold tailWord_2490276
  simp only [CollatzResearch.WordTrace]
  refine ⟨45413913763081416062813341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60551885017441888083751121 45413913763081416062813341)
  ·
    refine ⟨17030217661155531023555003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45413913763081416062813341 17030217661155531023555003)
    ·
      refine ⟨25545326491733296535332505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17030217661155531023555003 25545326491733296535332505)
      ·
        refine ⟨19158994868799972401499379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25545326491733296535332505 19158994868799972401499379)
        ·
          refine ⟨28738492303199958602249069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19158994868799972401499379 28738492303199958602249069)
          ·
            refine ⟨10776934613699984475843401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28738492303199958602249069 10776934613699984475843401)
            ·
              refine ⟨8082700960274988356882551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10776934613699984475843401 8082700960274988356882551)
              ·
                refine ⟨12124051440412482535323827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8082700960274988356882551 12124051440412482535323827)
                ·
                  refine ⟨18186077160618723802985741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12124051440412482535323827 18186077160618723802985741)
                  ·
                    refine ⟨6819778935232021426119653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18186077160618723802985741 6819778935232021426119653)
                    ·
                      refine ⟨1278708550356004017397435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6819778935232021426119653 1278708550356004017397435)
                      ·
                        rfl

theorem cell23_2490276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2490276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490276 prefixEnd_2490276 := by exact prefixLift 2490276
  have htrace : WordTrace (prefixWord ++ tailWord_2490276) baseStart_2490276 baseEnd_2490276 := by
    simpa [prefixWord, tailWord_2490276, baseEnd_2490276] using wordTrace_append hprefix tailTrace_2490276
  have hstable : (prefixWord ++ tailWord_2490276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490276).length < 2 ^ (prefixWord ++ tailWord_2490276).sum := by decide
  have hdescent : baseEnd_2490276 < baseStart_2490276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490293 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2490293 : Nat := 118140960795 + 2490293 * 2 ^ 59
def prefixEnd_2490293 : Nat := 4983230072969 + 3 ^ 40 * 2490293 * 2
def baseEnd_2490293 : Nat := 1278717279527130450884857

theorem tailTrace_2490293 : CollatzResearch.WordTrace tailWord_2490293 prefixEnd_2490293 1278717279527130450884857 := by
  unfold tailWord_2490293
  simp only [CollatzResearch.WordTrace]
  refine ⟨90828447567101244028995533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60552298378067496019330355 90828447567101244028995533)
  ·
    refine ⟨34060667837662966510873325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90828447567101244028995533 34060667837662966510873325)
    ·
      refine ⟨12772750439123612441577497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34060667837662966510873325 12772750439123612441577497)
      ·
        refine ⟨9579562829342709331183123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12772750439123612441577497 9579562829342709331183123)
        ·
          refine ⟨14369344244014063996774685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9579562829342709331183123 14369344244014063996774685)
          ·
            refine ⟨5388504091505273998790507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14369344244014063996774685 5388504091505273998790507)
            ·
              refine ⟨8082756137257910998185761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388504091505273998790507 8082756137257910998185761)
              ·
                refine ⟨6062067102943433248639321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8082756137257910998185761 6062067102943433248639321)
                ·
                  refine ⟨4546550327207574936479491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062067102943433248639321 4546550327207574936479491)
                  ·
                    refine ⟨6819825490811362404719237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4546550327207574936479491 6819825490811362404719237)
                    ·
                      refine ⟨1278717279527130450884857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6819825490811362404719237 1278717279527130450884857)
                      ·
                        rfl

theorem cell23_2490293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2490293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490293 prefixEnd_2490293 := by exact prefixLift 2490293
  have htrace : WordTrace (prefixWord ++ tailWord_2490293) baseStart_2490293 baseEnd_2490293 := by
    simpa [prefixWord, tailWord_2490293, baseEnd_2490293] using wordTrace_append hprefix tailTrace_2490293
  have hstable : (prefixWord ++ tailWord_2490293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490293).length < 2 ^ (prefixWord ++ tailWord_2490293).sum := by decide
  have hdescent : baseEnd_2490293 < baseStart_2490293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490330 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_2490330 : Nat := 118140960795 + 2490330 * 2 ^ 59
def prefixEnd_2490330 : Nat := 4983230072969 + 3 ^ 40 * 2490330 * 2
def baseEnd_2490330 : Nat := 1278736278311346806122187

theorem tailTrace_2490330 : CollatzResearch.WordTrace tailWord_2490330 prefixEnd_2490330 1278736278311346806122187 := by
  unfold tailWord_2490330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22707449266991799837023111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60553198045311466232061629 22707449266991799837023111)
  ·
    refine ⟨34061173900487699755534667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22707449266991799837023111 34061173900487699755534667)
    ·
      refine ⟨51091760850731549633302001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34061173900487699755534667 51091760850731549633302001)
      ·
        refine ⟨38318820638048662224976501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51091760850731549633302001 38318820638048662224976501)
        ·
          refine ⟨3592389434817062083591547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38318820638048662224976501 3592389434817062083591547)
          ·
            refine ⟨5388584152225593125387321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592389434817062083591547 5388584152225593125387321)
            ·
              refine ⟨4041438114169194844040491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388584152225593125387321 4041438114169194844040491)
              ·
                refine ⟨6062157171253792266060737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041438114169194844040491 6062157171253792266060737)
                ·
                  refine ⟨4546617878440344199545553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062157171253792266060737 4546617878440344199545553)
                  ·
                    refine ⟨3409963408830258149659165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546617878440344199545553 3409963408830258149659165)
                    ·
                      refine ⟨1278736278311346806122187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3409963408830258149659165 1278736278311346806122187)
                      ·
                        rfl

theorem cell23_2490330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_2490330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490330 prefixEnd_2490330 := by exact prefixLift 2490330
  have htrace : WordTrace (prefixWord ++ tailWord_2490330) baseStart_2490330 baseEnd_2490330 := by
    simpa [prefixWord, tailWord_2490330, baseEnd_2490330] using wordTrace_append hprefix tailTrace_2490330
  have hstable : (prefixWord ++ tailWord_2490330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490330).length < 2 ^ (prefixWord ++ tailWord_2490330).sum := by decide
  have hdescent : baseEnd_2490330 < baseStart_2490330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490381 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2490381 : Nat := 118140960795 + 2490381 * 2 ^ 59
def prefixEnd_2490381 : Nat := 4983230072969 + 3 ^ 40 * 2490381 * 2
def baseEnd_2490381 : Nat := 1278762465824726106584453

theorem tailTrace_2490381 : CollatzResearch.WordTrace tailWord_2490381 prefixEnd_2490381 1278762465824726106584453 := by
  unfold tailWord_2490381
  simp only [CollatzResearch.WordTrace]
  refine ⟨90831657190782435058198997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60554438127188290038799331 90831657190782435058198997)
  ·
    refine ⟨2128866965408963321676539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90831657190782435058198997 2128866965408963321676539)
    ·
      refine ⟨3193300448113444982514809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128866965408963321676539 3193300448113444982514809)
      ·
        refine ⟨2394975336085083736886107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3193300448113444982514809 2394975336085083736886107)
        ·
          refine ⟨3592463004127625605329161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394975336085083736886107 3592463004127625605329161)
          ·
            refine ⟨2694347253095719203996871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3592463004127625605329161 2694347253095719203996871)
            ·
              refine ⟨4041520879643578805995307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2694347253095719203996871 4041520879643578805995307)
              ·
                refine ⟨6062281319465368208992961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041520879643578805995307 6062281319465368208992961)
                ·
                  refine ⟨4546710989599026156744721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062281319465368208992961 4546710989599026156744721)
                  ·
                    refine ⟨3410033242199269617558541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546710989599026156744721 3410033242199269617558541)
                    ·
                      refine ⟨1278762465824726106584453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410033242199269617558541 1278762465824726106584453)
                      ·
                        rfl

theorem cell23_2490381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2490381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490381 prefixEnd_2490381 := by exact prefixLift 2490381
  have htrace : WordTrace (prefixWord ++ tailWord_2490381) baseStart_2490381 baseEnd_2490381 := by
    simpa [prefixWord, tailWord_2490381, baseEnd_2490381] using wordTrace_append hprefix tailTrace_2490381
  have hstable : (prefixWord ++ tailWord_2490381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490381).length < 2 ^ (prefixWord ++ tailWord_2490381).sum := by decide
  have hdescent : baseEnd_2490381 < baseStart_2490381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490397 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2490397 : Nat := 118140960795 + 2490397 * 2 ^ 59
def prefixEnd_2490397 : Nat := 4983230072969 + 3 ^ 40 * 2490397 * 2
def baseEnd_2490397 : Nat := 426256893838399347994793

theorem tailTrace_2490397 : CollatzResearch.WordTrace tailWord_2490397 prefixEnd_2490397 426256893838399347994793 := by
  unfold tailWord_2490397
  simp only [CollatzResearch.WordTrace]
  refine ⟨90832240758724469790781445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60554827172482979860520963 90832240758724469790781445)
  ·
    refine ⟨17031045142260838085771521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90832240758724469790781445 17031045142260838085771521)
    ·
      refine ⟨12773283856695628564328641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17031045142260838085771521 12773283856695628564328641)
      ·
        refine ⟨9579962892521721423246481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12773283856695628564328641 9579962892521721423246481)
        ·
          refine ⟨7184972169391291067434861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9579962892521721423246481 7184972169391291067434861)
          ·
            refine ⟨2694364563521734150288073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7184972169391291067434861 2694364563521734150288073)
            ·
              refine ⟨2020773422641300612716055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2694364563521734150288073 2020773422641300612716055)
              ·
                refine ⟨3031160133961950919074083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020773422641300612716055 3031160133961950919074083)
                ·
                  refine ⟨4546740200942926378611125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031160133961950919074083 4546740200942926378611125)
                  ·
                    refine ⟨426256893838399347994793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4546740200942926378611125 426256893838399347994793)
                    ·
                      rfl

theorem cell23_2490397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2490397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490397 prefixEnd_2490397 := by exact prefixLift 2490397
  have htrace : WordTrace (prefixWord ++ tailWord_2490397) baseStart_2490397 baseEnd_2490397 := by
    simpa [prefixWord, tailWord_2490397, baseEnd_2490397] using wordTrace_append hprefix tailTrace_2490397
  have hstable : (prefixWord ++ tailWord_2490397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490397).length < 2 ^ (prefixWord ++ tailWord_2490397).sum := by decide
  have hdescent : baseEnd_2490397 < baseStart_2490397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490410 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2490410 : Nat := 118140960795 + 2490410 * 2 ^ 59
def prefixEnd_2490410 : Nat := 4983230072969 + 3 ^ 40 * 2490410 * 2
def baseEnd_2490410 : Nat := 426259118921235497707273

theorem tailTrace_2490410 : CollatzResearch.WordTrace tailWord_2490410 prefixEnd_2490410 426259118921235497707273 := by
  unfold tailWord_2490410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22708178726919343252751171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60555143271784915340669789 22708178726919343252751171)
  ·
    refine ⟨34062268090379014879126757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22708178726919343252751171 34062268090379014879126757)
    ·
      refine ⟨6386675266946065289836267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34062268090379014879126757 6386675266946065289836267)
      ·
        refine ⟨9580012900419097934754401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386675266946065289836267 9580012900419097934754401)
        ·
          refine ⟨7185009675314323451065801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9580012900419097934754401 7185009675314323451065801)
          ·
            refine ⟨5388757256485742588299351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7185009675314323451065801 5388757256485742588299351)
            ·
              refine ⟨8083135884728613882449027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388757256485742588299351 8083135884728613882449027)
              ·
                refine ⟨12124703827092920823673541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083135884728613882449027 12124703827092920823673541)
                ·
                  refine ⟨2273381967579922654438789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12124703827092920823673541 2273381967579922654438789)
                  ·
                    refine ⟨426259118921235497707273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2273381967579922654438789 426259118921235497707273)
                    ·
                      rfl

theorem cell23_2490410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2490410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490410 prefixEnd_2490410 := by exact prefixLift 2490410
  have htrace : WordTrace (prefixWord ++ tailWord_2490410) baseStart_2490410 baseEnd_2490410 := by
    simpa [prefixWord, tailWord_2490410, baseEnd_2490410] using wordTrace_append hprefix tailTrace_2490410
  have hstable : (prefixWord ++ tailWord_2490410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490410).length < 2 ^ (prefixWord ++ tailWord_2490410).sum := by decide
  have hdescent : baseEnd_2490410 < baseStart_2490410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490417 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_2490417 : Nat := 118140960795 + 2490417 * 2 ^ 59
def prefixEnd_2490417 : Nat := 4983230072969 + 3 ^ 40 * 2490417 * 2
def baseEnd_2490417 : Nat := 1278780951128287965734287

theorem tailTrace_2490417 : CollatzResearch.WordTrace tailWord_2490417 prefixEnd_2490417 1278780951128287965734287 := by
  unfold tailWord_2490417
  simp only [CollatzResearch.WordTrace]
  refine ⟨90832970218652013206509505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60555313479101342137673003 90832970218652013206509505)
  ·
    refine ⟨68124727663989009904882129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90832970218652013206509505 68124727663989009904882129)
    ·
      refine ⟨51093545747991757428661597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68124727663989009904882129 51093545747991757428661597)
      ·
        refine ⟨19160079655496909035748099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51093545747991757428661597 19160079655496909035748099)
        ·
          refine ⟨28740119483245363553622149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19160079655496909035748099 28740119483245363553622149)
          ·
            refine ⟨5388772403108505666304153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28740119483245363553622149 5388772403108505666304153)
            ·
              refine ⟨4041579302331379249728115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388772403108505666304153 4041579302331379249728115)
              ·
                refine ⟨6062368953497068874592173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041579302331379249728115 6062368953497068874592173)
                ·
                  refine ⟨2273388357561400827972065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6062368953497068874592173 2273388357561400827972065)
                  ·
                    refine ⟨1705041268171050620979049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2273388357561400827972065 1705041268171050620979049)
                    ·
                      refine ⟨1278780951128287965734287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705041268171050620979049 1278780951128287965734287)
                      ·
                        rfl

theorem cell23_2490417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_2490417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490417 prefixEnd_2490417 := by exact prefixLift 2490417
  have htrace : WordTrace (prefixWord ++ tailWord_2490417) baseStart_2490417 baseEnd_2490417 := by
    simpa [prefixWord, tailWord_2490417, baseEnd_2490417] using wordTrace_append hprefix tailTrace_2490417
  have hstable : (prefixWord ++ tailWord_2490417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490417).length < 2 ^ (prefixWord ++ tailWord_2490417).sum := by decide
  have hdescent : baseEnd_2490417 < baseStart_2490417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490430 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2490430 : Nat := 118140960795 + 2490430 * 2 ^ 59
def prefixEnd_2490430 : Nat := 4983230072969 + 3 ^ 40 * 2490430 * 2
def baseEnd_2490430 : Nat := 1278787626376796414871727

theorem tailTrace_2490430 : CollatzResearch.WordTrace tailWord_2490430 prefixEnd_2490430 1278787626376796414871727 := by
  unfold tailWord_2490430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354180545950614553341593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60555629578403277617821829 11354180545950614553341593)
  ·
    refine ⟨8515635409462960915006195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11354180545950614553341593 8515635409462960915006195)
    ·
      refine ⟨12773453114194441372509293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8515635409462960915006195 12773453114194441372509293)
      ·
        refine ⟨4790044917822915514690985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12773453114194441372509293 4790044917822915514690985)
        ·
          refine ⟨3592533688367186636018239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4790044917822915514690985 3592533688367186636018239)
          ·
            refine ⟨5388800532550779954027359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592533688367186636018239 5388800532550779954027359)
            ·
              refine ⟨8083200798826169931041039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5388800532550779954027359 8083200798826169931041039)
              ·
                refine ⟨12124801198239254896561559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083200798826169931041039 12124801198239254896561559)
                ·
                  refine ⟨18187201797358882344842339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12124801198239254896561559 18187201797358882344842339)
                  ·
                    refine ⟨27280802696038323517263509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18187201797358882344842339 27280802696038323517263509)
                    ·
                      refine ⟨1278787626376796414871727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27280802696038323517263509 1278787626376796414871727)
                      ·
                        rfl

theorem cell23_2490430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2490430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490430 prefixEnd_2490430 := by exact prefixLift 2490430
  have htrace : WordTrace (prefixWord ++ tailWord_2490430) baseStart_2490430 baseEnd_2490430 := by
    simpa [prefixWord, tailWord_2490430, baseEnd_2490430] using wordTrace_append hprefix tailTrace_2490430
  have hstable : (prefixWord ++ tailWord_2490430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490430).length < 2 ^ (prefixWord ++ tailWord_2490430).sum := by decide
  have hdescent : baseEnd_2490430 < baseStart_2490430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490454 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2490454 : Nat := 118140960795 + 2490454 * 2 ^ 59
def prefixEnd_2490454 : Nat := 4983230072969 + 3 ^ 40 * 2490454 * 2
def baseEnd_2490454 : Nat := 1278799949912504320971617

theorem tailTrace_2490454 : CollatzResearch.WordTrace tailWord_2490454 prefixEnd_2490454 1278799949912504320971617 := by
  unfold tailWord_2490454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677144982469873032850401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60556213146345312350404277 5677144982469873032850401)
  ·
    refine ⟨4257858736852404774637801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5677144982469873032850401 4257858736852404774637801)
    ·
      refine ⟨3193394052639303580978351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4257858736852404774637801 3193394052639303580978351)
      ·
        refine ⟨4790091078958955371467527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193394052639303580978351 4790091078958955371467527)
        ·
          refine ⟨7185136618438433057201291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790091078958955371467527 7185136618438433057201291)
          ·
            refine ⟨10777704927657649585801937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185136618438433057201291 10777704927657649585801937)
            ·
              refine ⟨8083278695743237189351453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10777704927657649585801937 8083278695743237189351453)
              ·
                refine ⟨3031229510903713946006795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8083278695743237189351453 3031229510903713946006795)
                ·
                  refine ⟨4546844266355570919010193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031229510903713946006795 4546844266355570919010193)
                  ·
                    refine ⟨3410133199766678189257645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4546844266355570919010193 3410133199766678189257645)
                    ·
                      refine ⟨1278799949912504320971617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410133199766678189257645 1278799949912504320971617)
                      ·
                        rfl

theorem cell23_2490454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2490454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490454 prefixEnd_2490454 := by exact prefixLift 2490454
  have htrace : WordTrace (prefixWord ++ tailWord_2490454) baseStart_2490454 baseEnd_2490454 := by
    simpa [prefixWord, tailWord_2490454, baseEnd_2490454] using wordTrace_append hprefix tailTrace_2490454
  have hstable : (prefixWord ++ tailWord_2490454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490454).length < 2 ^ (prefixWord ++ tailWord_2490454).sum := by decide
  have hdescent : baseEnd_2490454 < baseStart_2490454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490493 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2490493 : Nat := 118140960795 + 2490493 * 2 ^ 59
def prefixEnd_2490493 : Nat := 4983230072969 + 3 ^ 40 * 2490493 * 2
def baseEnd_2490493 : Nat := 1278819975658029668383937

theorem tailTrace_2490493 : CollatzResearch.WordTrace tailWord_2490493 prefixEnd_2490493 1278819975658029668383937 := by
  unfold tailWord_2490493
  simp only [CollatzResearch.WordTrace]
  refine ⟨90835742166376678186276133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60557161444251118790850755 90835742166376678186276133)
  ·
    refine ⟨17031701656195627159926775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90835742166376678186276133 17031701656195627159926775)
    ·
      refine ⟨25547552484293440739890163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17031701656195627159926775 25547552484293440739890163)
      ·
        refine ⟨38321328726440161109835245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25547552484293440739890163 38321328726440161109835245)
        ·
          refine ⟨14370498272415060416188217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38321328726440161109835245 14370498272415060416188217)
          ·
            refine ⟨10777873704311295312141163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14370498272415060416188217 10777873704311295312141163)
            ·
              refine ⟨16166810556466942968211745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10777873704311295312141163 16166810556466942968211745)
              ·
                refine ⟨12125107917350207226158809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16166810556466942968211745 12125107917350207226158809)
                ·
                  refine ⟨9093830938012655419619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12125107917350207226158809 9093830938012655419619107)
                  ·
                    refine ⟨13640746407018983129428661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9093830938012655419619107 13640746407018983129428661)
                    ·
                      refine ⟨1278819975658029668383937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13640746407018983129428661 1278819975658029668383937)
                      ·
                        rfl

theorem cell23_2490493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2490493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490493 prefixEnd_2490493 := by exact prefixLift 2490493
  have htrace : WordTrace (prefixWord ++ tailWord_2490493) baseStart_2490493 baseEnd_2490493 := by
    simpa [prefixWord, tailWord_2490493, baseEnd_2490493] using wordTrace_append hprefix tailTrace_2490493
  have hstable : (prefixWord ++ tailWord_2490493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490493).length < 2 ^ (prefixWord ++ tailWord_2490493).sum := by decide
  have hdescent : baseEnd_2490493 < baseStart_2490493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490496 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 9]
def baseStart_2490496 : Nat := 118140960795 + 2490496 * 2 ^ 59
def prefixEnd_2490496 : Nat := 4983230072969 + 3 ^ 40 * 2490496 * 2
def baseEnd_2490496 : Nat := 142091279566665906294047

theorem tailTrace_2490496 : CollatzResearch.WordTrace tailWord_2490496 prefixEnd_2490496 142091279566665906294047 := by
  unfold tailWord_2490496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45417925792682904849317671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60557234390243873132423561 45417925792682904849317671)
  ·
    refine ⟨68126888689024357273976507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45417925792682904849317671 68126888689024357273976507)
    ·
      refine ⟨102190333033536535910964761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68126888689024357273976507 102190333033536535910964761)
      ·
        refine ⟨76642749775152401933223571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102190333033536535910964761 76642749775152401933223571)
        ·
          refine ⟨114964124662728602899835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76642749775152401933223571 114964124662728602899835357)
          ·
            refine ⟨43111546748523226087438259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114964124662728602899835357 43111546748523226087438259)
            ·
              refine ⟨64667320122784839131157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43111546748523226087438259 64667320122784839131157389)
              ·
                refine ⟨24250245046044314674184021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64667320122784839131157389 24250245046044314674184021)
                ·
                  refine ⟨142091279566665906294047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24250245046044314674184021 142091279566665906294047)
                  ·
                    rfl

theorem cell23_2490496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_2490496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490496 prefixEnd_2490496 := by exact prefixLift 2490496
  have htrace : WordTrace (prefixWord ++ tailWord_2490496) baseStart_2490496 baseEnd_2490496 := by
    simpa [prefixWord, tailWord_2490496, baseEnd_2490496] using wordTrace_append hprefix tailTrace_2490496
  have hstable : (prefixWord ++ tailWord_2490496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490496).length < 2 ^ (prefixWord ++ tailWord_2490496).sum := by decide
  have hdescent : baseEnd_2490496 < baseStart_2490496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490524 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2490524 : Nat := 118140960795 + 2490524 * 2 ^ 59
def prefixEnd_2490524 : Nat := 4983230072969 + 3 ^ 40 * 2490524 * 2
def baseEnd_2490524 : Nat := 1278835893558319047096295

theorem tailTrace_2490524 : CollatzResearch.WordTrace tailWord_2490524 prefixEnd_2490524 1278835893558319047096295 := by
  unfold tailWord_2490524
  simp only [CollatzResearch.WordTrace]
  refine ⟨45418436414632185240327313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60557915219509580320436417 45418436414632185240327313)
  ·
    refine ⟨34063827310974138930245485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45418436414632185240327313 34063827310974138930245485)
    ·
      refine ⟨12773935241615302098842057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34063827310974138930245485 12773935241615302098842057)
      ·
        refine ⟨9580451431211476574131543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12773935241615302098842057 9580451431211476574131543)
        ·
          refine ⟨14370677146817214861197315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9580451431211476574131543 14370677146817214861197315)
          ·
            refine ⟨21556015720225822291795973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14370677146817214861197315 21556015720225822291795973)
            ·
              refine ⟨4041752947542341679711745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21556015720225822291795973 4041752947542341679711745)
              ·
                refine ⟨3031314710656756259783809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4041752947542341679711745 3031314710656756259783809)
                ·
                  refine ⟨2273486032992567194837857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3031314710656756259783809 2273486032992567194837857)
                  ·
                    refine ⟨1705114524744425396128393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2273486032992567194837857 1705114524744425396128393)
                    ·
                      refine ⟨1278835893558319047096295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705114524744425396128393 1278835893558319047096295)
                      ·
                        rfl

theorem cell23_2490524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2490524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490524 prefixEnd_2490524 := by exact prefixLift 2490524
  have htrace : WordTrace (prefixWord ++ tailWord_2490524) baseStart_2490524 baseEnd_2490524 := by
    simpa [prefixWord, tailWord_2490524, baseEnd_2490524] using wordTrace_append hprefix tailTrace_2490524
  have hstable : (prefixWord ++ tailWord_2490524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490524).length < 2 ^ (prefixWord ++ tailWord_2490524).sum := by decide
  have hdescent : baseEnd_2490524 < baseStart_2490524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490560 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_2490560 : Nat := 118140960795 + 2490560 * 2 ^ 59
def prefixEnd_2490560 : Nat := 4983230072969 + 3 ^ 40 * 2490560 * 2
def baseEnd_2490560 : Nat := 426284792953960302082043

theorem tailTrace_2490560 : CollatzResearch.WordTrace tailWord_2490560 prefixEnd_2490560 426284792953960302082043 := by
  unfold tailWord_2490560
  simp only [CollatzResearch.WordTrace]
  refine ⟨45419092928566974314482567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60558790571422632419310089 45419092928566974314482567)
  ·
    refine ⟨68128639392850461471723851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45419092928566974314482567 68128639392850461471723851)
    ·
      refine ⟨102192959089275692207585777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68128639392850461471723851 102192959089275692207585777)
      ·
        refine ⟨76644719316956769155689333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102192959089275692207585777 76644719316956769155689333)
        ·
          refine ⟨7185442435964697108345875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76644719316956769155689333 7185442435964697108345875)
          ·
            refine ⟨10778163653947045662518813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185442435964697108345875 10778163653947045662518813)
            ·
              refine ⟨4041811370230142123444555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10778163653947045662518813 4041811370230142123444555)
              ·
                refine ⟨6062717055345213185166833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041811370230142123444555 6062717055345213185166833)
                ·
                  refine ⟨4547037791508909888875125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6062717055345213185166833 4547037791508909888875125)
                  ·
                    refine ⟨426284792953960302082043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4547037791508909888875125 426284792953960302082043)
                    ·
                      rfl

theorem cell23_2490560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_2490560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490560 prefixEnd_2490560 := by exact prefixLift 2490560
  have htrace : WordTrace (prefixWord ++ tailWord_2490560) baseStart_2490560 baseEnd_2490560 := by
    simpa [prefixWord, tailWord_2490560, baseEnd_2490560] using wordTrace_append hprefix tailTrace_2490560
  have hstable : (prefixWord ++ tailWord_2490560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490560).length < 2 ^ (prefixWord ++ tailWord_2490560).sum := by decide
  have hdescent : baseEnd_2490560 < baseStart_2490560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490593 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2490593 : Nat := 118140960795 + 2490593 * 2 ^ 59
def prefixEnd_2490593 : Nat := 4983230072969 + 3 ^ 40 * 2490593 * 2
def baseEnd_2490593 : Nat := 1278871323723479277133477

theorem tailTrace_2490593 : CollatzResearch.WordTrace tailWord_2490593 prefixEnd_2490593 1278871323723479277133477 := by
  unfold tailWord_2490593
  simp only [CollatzResearch.WordTrace]
  refine ⟨90839389466014395264916433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60559592977342930176610955 90839389466014395264916433)
  ·
    refine ⟨68129542099510796448687325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90839389466014395264916433 68129542099510796448687325)
    ·
      refine ⟨25548578287316548668257747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68129542099510796448687325 25548578287316548668257747)
      ·
        refine ⟨38322867430974823002386621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25548578287316548668257747 38322867430974823002386621)
        ·
          refine ⟨14371075286615558625894983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38322867430974823002386621 14371075286615558625894983)
          ·
            refine ⟨21556612929923337938842475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14371075286615558625894983 21556612929923337938842475)
            ·
              refine ⟨32334919394885006908263713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21556612929923337938842475 32334919394885006908263713)
              ·
                refine ⟨24251189546163755181197785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32334919394885006908263713 24251189546163755181197785)
                ·
                  refine ⟨18188392159622816385898339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24251189546163755181197785 18188392159622816385898339)
                  ·
                    refine ⟨27282588239434224578847509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18188392159622816385898339 27282588239434224578847509)
                    ·
                      refine ⟨1278871323723479277133477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27282588239434224578847509 1278871323723479277133477)
                      ·
                        rfl

theorem cell23_2490593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2490593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490593 prefixEnd_2490593 := by exact prefixLift 2490593
  have htrace : WordTrace (prefixWord ++ tailWord_2490593) baseStart_2490593 baseEnd_2490593 := by
    simpa [prefixWord, tailWord_2490593, baseEnd_2490593] using wordTrace_append hprefix tailTrace_2490593
  have hstable : (prefixWord ++ tailWord_2490593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490593).length < 2 ^ (prefixWord ++ tailWord_2490593).sum := by decide
  have hdescent : baseEnd_2490593 < baseStart_2490593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490597 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2490597 : Nat := 118140960795 + 2490597 * 2 ^ 59
def prefixEnd_2490597 : Nat := 4983230072969 + 3 ^ 40 * 2490597 * 2
def baseEnd_2490597 : Nat := 1278873377646097261483459

theorem tailTrace_2490597 : CollatzResearch.WordTrace tailWord_2490597 prefixEnd_2490597 1278873377646097261483459 := by
  unfold tailWord_2490597
  simp only [CollatzResearch.WordTrace]
  refine ⟨90839535357999903948062045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60559690238666602632041363 90839535357999903948062045)
  ·
    refine ⟨34064825759249963980523267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90839535357999903948062045 34064825759249963980523267)
    ·
      refine ⟨51097238638874945970784901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34064825759249963980523267 51097238638874945970784901)
      ·
        refine ⟨9580732244789052369522169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51097238638874945970784901 9580732244789052369522169)
        ·
          refine ⟨7185549183591789277141627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9580732244789052369522169 7185549183591789277141627)
          ·
            refine ⟨10778323775387683915712441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185549183591789277141627 10778323775387683915712441)
            ·
              refine ⟨8083742831540762936784331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10778323775387683915712441 8083742831540762936784331)
              ·
                refine ⟨12125614247311144405176497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083742831540762936784331 12125614247311144405176497)
                ·
                  refine ⟨9094210685483358303882373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12125614247311144405176497 9094210685483358303882373)
                  ·
                    refine ⟨1705164503528129681977945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9094210685483358303882373 1705164503528129681977945)
                    ·
                      refine ⟨1278873377646097261483459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705164503528129681977945 1278873377646097261483459)
                      ·
                        rfl

theorem cell23_2490597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2490597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490597 prefixEnd_2490597 := by exact prefixLift 2490597
  have htrace : WordTrace (prefixWord ++ tailWord_2490597) baseStart_2490597 baseEnd_2490597 := by
    simpa [prefixWord, tailWord_2490597, baseEnd_2490597] using wordTrace_append hprefix tailTrace_2490597
  have hstable : (prefixWord ++ tailWord_2490597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490597).length < 2 ^ (prefixWord ++ tailWord_2490597).sum := by decide
  have hdescent : baseEnd_2490597 < baseStart_2490597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490600 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2490600 : Nat := 118140960795 + 2490600 * 2 ^ 59
def prefixEnd_2490600 : Nat := 4983230072969 + 3 ^ 40 * 2490600 * 2
def baseEnd_2490600 : Nat := 1278874918088060749745945

theorem tailTrace_2490600 : CollatzResearch.WordTrace tailWord_2490600 prefixEnd_2490600 1278874918088060749745945 := by
  unfold tailWord_2490600
  simp only [CollatzResearch.WordTrace]
  refine ⟨45419822388494517730210627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60559763184659356973614169 45419822388494517730210627)
  ·
    refine ⟨68129733582741776595315941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45419822388494517730210627 68129733582741776595315941)
    ·
      refine ⟨12774325046764083111621739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68129733582741776595315941 12774325046764083111621739)
      ·
        refine ⟨19161487570146124667432609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774325046764083111621739 19161487570146124667432609)
        ·
          refine ⟨14371115677609593500574457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19161487570146124667432609 14371115677609593500574457)
          ·
            refine ⟨10778336758207195125430843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14371115677609593500574457 10778336758207195125430843)
            ·
              refine ⟨16167505137310792688146265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10778336758207195125430843 16167505137310792688146265)
              ·
                refine ⟨12125628852983094516109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16167505137310792688146265 12125628852983094516109699)
                ·
                  refine ⟨18188443279474641774164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12125628852983094516109699 18188443279474641774164549)
                  ·
                    refine ⟨3410333114901495332655853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18188443279474641774164549 3410333114901495332655853)
                    ·
                      refine ⟨1278874918088060749745945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410333114901495332655853 1278874918088060749745945)
                      ·
                        rfl

theorem cell23_2490600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2490600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490600 prefixEnd_2490600 := by exact prefixLift 2490600
  have htrace : WordTrace (prefixWord ++ tailWord_2490600) baseStart_2490600 baseEnd_2490600 := by
    simpa [prefixWord, tailWord_2490600, baseEnd_2490600] using wordTrace_append hprefix tailTrace_2490600
  have hstable : (prefixWord ++ tailWord_2490600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490600).length < 2 ^ (prefixWord ++ tailWord_2490600).sum := by decide
  have hdescent : baseEnd_2490600 < baseStart_2490600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490654 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2490654 : Nat := 118140960795 + 2490654 * 2 ^ 59
def prefixEnd_2490654 : Nat := 4983230072969 + 3 ^ 40 * 2490654 * 2
def baseEnd_2490654 : Nat := 142100294004822615385633

theorem tailTrace_2490654 : CollatzResearch.WordTrace tailWord_2490654 prefixEnd_2490654 142100294004822615385633 := by
  unfold tailWord_2490654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355201789849175335360877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60561076212528935121924677 11355201789849175335360877)
  ·
    refine ⟨4258200671193440750760329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11355201789849175335360877 4258200671193440750760329)
    ·
      refine ⟨3193650503395080563070247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4258200671193440750760329 3193650503395080563070247)
      ·
        refine ⟨4790475755092620844605371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193650503395080563070247 4790475755092620844605371)
        ·
          refine ⟨7185713632638931266908057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790475755092620844605371 7185713632638931266908057)
          ·
            refine ⟨5389285224479198450181043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7185713632638931266908057 5389285224479198450181043)
            ·
              refine ⟨8083927836718797675271565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389285224479198450181043 8083927836718797675271565)
              ·
                refine ⟨3031472938769549128226837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8083927836718797675271565 3031472938769549128226837)
                ·
                  refine ⟨142100294004822615385633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3031472938769549128226837 142100294004822615385633)
                  ·
                    rfl

theorem cell23_2490654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2490654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490654 prefixEnd_2490654 := by exact prefixLift 2490654
  have htrace : WordTrace (prefixWord ++ tailWord_2490654) baseStart_2490654 baseEnd_2490654 := by
    simpa [prefixWord, tailWord_2490654, baseEnd_2490654] using wordTrace_append hprefix tailTrace_2490654
  have hstable : (prefixWord ++ tailWord_2490654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490654).length < 2 ^ (prefixWord ++ tailWord_2490654).sum := by decide
  have hdescent : baseEnd_2490654 < baseStart_2490654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490680 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_2490680 : Nat := 118140960795 + 2490680 * 2 ^ 59
def prefixEnd_2490680 : Nat := 4983230072969 + 3 ^ 40 * 2490680 * 2
def baseEnd_2490680 : Nat := 426305332180140145581859

theorem tailTrace_2490680 : CollatzResearch.WordTrace tailWord_2490680 prefixEnd_2490680 426305332180140145581859 := by
  unfold tailWord_2490680
  simp only [CollatzResearch.WordTrace]
  refine ⟨45421281308349604561666747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60561708411132806082222329 45421281308349604561666747)
  ·
    refine ⟨68131921962524406842500121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45421281308349604561666747 68131921962524406842500121)
    ·
      refine ⟨51098941471893305131875091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68131921962524406842500121 51098941471893305131875091)
      ·
        refine ⟨76648412207839957697812637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51098941471893305131875091 76648412207839957697812637)
        ·
          refine ⟨28743154577939984136679739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76648412207839957697812637 28743154577939984136679739)
          ·
            refine ⟨43114731866909976205019609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28743154577939984136679739 43114731866909976205019609)
            ·
              refine ⟨32336048900182482153764707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43114731866909976205019609 32336048900182482153764707)
              ·
                refine ⟨48504073350273723230647061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32336048900182482153764707 48504073350273723230647061)
                ·
                  refine ⟨2273628438294080776436581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48504073350273723230647061 2273628438294080776436581)
                  ·
                    refine ⟨426305332180140145581859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2273628438294080776436581 426305332180140145581859)
                    ·
                      rfl

theorem cell23_2490680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_2490680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490680 prefixEnd_2490680 := by exact prefixLift 2490680
  have htrace : WordTrace (prefixWord ++ tailWord_2490680) baseStart_2490680 baseEnd_2490680 := by
    simpa [prefixWord, tailWord_2490680, baseEnd_2490680] using wordTrace_append hprefix tailTrace_2490680
  have hstable : (prefixWord ++ tailWord_2490680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490680).length < 2 ^ (prefixWord ++ tailWord_2490680).sum := by decide
  have hdescent : baseEnd_2490680 < baseStart_2490680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490700 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2490700 : Nat := 118140960795 + 2490700 * 2 ^ 59
def prefixEnd_2490700 : Nat := 4983230072969 + 3 ^ 40 * 2490700 * 2
def baseEnd_2490700 : Nat := 1278926266153510358495485

theorem tailTrace_2490700 : CollatzResearch.WordTrace tailWord_2490700 prefixEnd_2490700 1278926266153510358495485 := by
  unfold tailWord_2490700
  simp only [CollatzResearch.WordTrace]
  refine ⟨45421646038313376269530777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60562194717751168359374369 45421646038313376269530777)
  ·
    refine ⟨34066234528735032202148083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45421646038313376269530777 34066234528735032202148083)
    ·
      refine ⟨51099351793102548303222125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34066234528735032202148083 51099351793102548303222125)
      ·
        refine ⟨19162256922413455613708297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51099351793102548303222125 19162256922413455613708297)
        ·
          refine ⟨14371692691810091710281223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19162256922413455613708297 14371692691810091710281223)
          ·
            refine ⟨21557539037715137565421835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14371692691810091710281223 21557539037715137565421835)
            ·
              refine ⟨32336308556572706348132753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21557539037715137565421835 32336308556572706348132753)
              ·
                refine ⟨24252231417429529761099565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32336308556572706348132753 24252231417429529761099565)
                ·
                  refine ⟨9094586781536073660412337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24252231417429529761099565 9094586781536073660412337)
                  ·
                    refine ⟨6820940086152055245309253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9094586781536073660412337 6820940086152055245309253)
                    ·
                      refine ⟨1278926266153510358495485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6820940086152055245309253 1278926266153510358495485)
                      ·
                        rfl

theorem cell23_2490700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2490700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490700 prefixEnd_2490700 := by exact prefixLift 2490700
  have htrace : WordTrace (prefixWord ++ tailWord_2490700) baseStart_2490700 baseEnd_2490700 := by
    simpa [prefixWord, tailWord_2490700, baseEnd_2490700] using wordTrace_append hprefix tailTrace_2490700
  have hstable : (prefixWord ++ tailWord_2490700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490700).length < 2 ^ (prefixWord ++ tailWord_2490700).sum := by decide
  have hdescent : baseEnd_2490700 < baseStart_2490700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490703 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_2490703 : Nat := 118140960795 + 2490703 * 2 ^ 59
def prefixEnd_2490703 : Nat := 4983230072969 + 3 ^ 40 * 2490703 * 2
def baseEnd_2490703 : Nat := 1278927806595473846757971

theorem tailTrace_2490703 : CollatzResearch.WordTrace tailWord_2490703 prefixEnd_2490703 1278927806595473846757971 := by
  unfold tailWord_2490703
  simp only [CollatzResearch.WordTrace]
  refine ⟨90843401495615884051420763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60562267663743922700947175 90843401495615884051420763)
  ·
    refine ⟨136265102243423826077131145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90843401495615884051420763 136265102243423826077131145)
    ·
      refine ⟨102198826682567869557848359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136265102243423826077131145 102198826682567869557848359)
      ·
        refine ⟨153298240023851804336772539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102198826682567869557848359 153298240023851804336772539)
        ·
          refine ⟨229947360035777706505158809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153298240023851804336772539 229947360035777706505158809)
          ·
            refine ⟨172460520026833279878869107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229947360035777706505158809 172460520026833279878869107)
            ·
              refine ⟨258690780040249919818303661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172460520026833279878869107 258690780040249919818303661)
              ·
                refine ⟨97009042515093719931863873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258690780040249919818303661 97009042515093719931863873)
                ·
                  refine ⟨72756781886320289948897905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97009042515093719931863873 72756781886320289948897905)
                  ·
                    refine ⟨54567586414740217461673429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72756781886320289948897905 54567586414740217461673429)
                    ·
                      refine ⟨1278927806595473846757971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54567586414740217461673429 1278927806595473846757971)
                      ·
                        rfl

theorem cell23_2490703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_2490703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490703 prefixEnd_2490703 := by exact prefixLift 2490703
  have htrace : WordTrace (prefixWord ++ tailWord_2490703) baseStart_2490703 baseEnd_2490703 := by
    simpa [prefixWord, tailWord_2490703, baseEnd_2490703] using wordTrace_append hprefix tailTrace_2490703
  have hstable : (prefixWord ++ tailWord_2490703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490703).length < 2 ^ (prefixWord ++ tailWord_2490703).sum := by decide
  have hdescent : baseEnd_2490703 < baseStart_2490703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490727 : List Nat := [1, 1, 5, 1, 3, 2, 3, 7]
def baseStart_2490727 : Nat := 118140960795 + 2490727 * 2 ^ 59
def prefixEnd_2490727 : Nat := 4983230072969 + 3 ^ 40 * 2490727 * 2
def baseEnd_2490727 : Nat := 47368152967821546402143

theorem tailTrace_2490727 : CollatzResearch.WordTrace tailWord_2490727 prefixEnd_2490727 47368152967821546402143 := by
  unfold tailWord_2490727
  simp only [CollatzResearch.WordTrace]
  refine ⟨90844276847528936150294435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60562851231685957433529623 90844276847528936150294435)
  ·
    refine ⟨136266415271293404225441653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90844276847528936150294435 136266415271293404225441653)
    ·
      refine ⟨12774976431683756646135155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136266415271293404225441653 12774976431683756646135155)
      ·
        refine ⟨19162464647525634969202733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774976431683756646135155 19162464647525634969202733)
        ·
          refine ⟨7185924242822113113451025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19162464647525634969202733 7185924242822113113451025)
          ·
            refine ⟨5389443182116584835088269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7185924242822113113451025 5389443182116584835088269)
            ·
              refine ⟨2021041193293719313158101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5389443182116584835088269 2021041193293719313158101)
              ·
                refine ⟨47368152967821546402143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2021041193293719313158101 47368152967821546402143)
                ·
                  rfl

theorem cell23_2490727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 7].length) (baseStart_2490727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490727 prefixEnd_2490727 := by exact prefixLift 2490727
  have htrace : WordTrace (prefixWord ++ tailWord_2490727) baseStart_2490727 baseEnd_2490727 := by
    simpa [prefixWord, tailWord_2490727, baseEnd_2490727] using wordTrace_append hprefix tailTrace_2490727
  have hstable : (prefixWord ++ tailWord_2490727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490727).length < 2 ^ (prefixWord ++ tailWord_2490727).sum := by decide
  have hdescent : baseEnd_2490727 < baseStart_2490727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490737 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_2490737 : Nat := 118140960795 + 2490737 * 2 ^ 59
def prefixEnd_2490737 : Nat := 4983230072969 + 3 ^ 40 * 2490737 * 2
def baseEnd_2490737 : Nat := 1278945264937726713732815

theorem tailTrace_2490737 : CollatzResearch.WordTrace tailWord_2490737 prefixEnd_2490737 1278945264937726713732815 := by
  unfold tailWord_2490737
  simp only [CollatzResearch.WordTrace]
  refine ⟨90844641577492707858158465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60563094384995138572105643 90844641577492707858158465)
  ·
    refine ⟨68133481183119530893618849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90844641577492707858158465 68133481183119530893618849)
    ·
      refine ⟨51100110887339648170214137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68133481183119530893618849 51100110887339648170214137)
      ·
        refine ⟨38325083165504736127660603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51100110887339648170214137 38325083165504736127660603)
        ·
          refine ⟨57487624748257104191490905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38325083165504736127660603 57487624748257104191490905)
          ·
            refine ⟨43115718561192828143618179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57487624748257104191490905 43115718561192828143618179)
            ·
              refine ⟨64673577841789242215427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43115718561192828143618179 64673577841789242215427269)
              ·
                refine ⟨12126295845335482915392613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64673577841789242215427269 12126295845335482915392613)
                ·
                  refine ⟨2273680471000403046636115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12126295845335482915392613 2273680471000403046636115)
                  ·
                    refine ⟨3410520706500604569954173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2273680471000403046636115 3410520706500604569954173)
                    ·
                      refine ⟨1278945264937726713732815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410520706500604569954173 1278945264937726713732815)
                      ·
                        rfl

theorem cell23_2490737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_2490737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490737 prefixEnd_2490737 := by exact prefixLift 2490737
  have htrace : WordTrace (prefixWord ++ tailWord_2490737) baseStart_2490737 baseEnd_2490737 := by
    simpa [prefixWord, tailWord_2490737, baseEnd_2490737] using wordTrace_append hprefix tailTrace_2490737
  have hstable : (prefixWord ++ tailWord_2490737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490737).length < 2 ^ (prefixWord ++ tailWord_2490737).sum := by decide
  have hdescent : baseEnd_2490737 < baseStart_2490737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490738 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_2490738 : Nat := 118140960795 + 2490738 * 2 ^ 59
def prefixEnd_2490738 : Nat := 4983230072969 + 3 ^ 40 * 2490738 * 2
def baseEnd_2490738 : Nat := 1278945778418381209820311

theorem tailTrace_2490738 : CollatzResearch.WordTrace tailWord_2490738 prefixEnd_2490738 1278945778418381209820311 := by
  unfold tailWord_2490738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22711169512622271257236217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60563118700326056685963245 22711169512622271257236217)
  ·
    refine ⟨17033377134466703442927163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22711169512622271257236217 17033377134466703442927163)
    ·
      refine ⟨25550065701700055164390745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17033377134466703442927163 25550065701700055164390745)
      ·
        refine ⟨19162549276275041373293059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25550065701700055164390745 19162549276275041373293059)
        ·
          refine ⟨28743823914412562059939589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19162549276275041373293059 28743823914412562059939589)
          ·
            refine ⟨5389466983952355386238673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28743823914412562059939589 5389466983952355386238673)
            ·
              refine ⟨4042100237964266539679005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5389466983952355386238673 4042100237964266539679005)
              ·
                refine ⟨1515787589236599952379627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4042100237964266539679005 1515787589236599952379627)
                ·
                  refine ⟨2273681383854899928569441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515787589236599952379627 2273681383854899928569441)
                  ·
                    refine ⟨1705261037891174946427081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2273681383854899928569441 1705261037891174946427081)
                    ·
                      refine ⟨1278945778418381209820311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705261037891174946427081 1278945778418381209820311)
                      ·
                        rfl

theorem cell23_2490738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_2490738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490738 prefixEnd_2490738 := by exact prefixLift 2490738
  have htrace : WordTrace (prefixWord ++ tailWord_2490738) baseStart_2490738 baseEnd_2490738 := by
    simpa [prefixWord, tailWord_2490738, baseEnd_2490738] using wordTrace_append hprefix tailTrace_2490738
  have hstable : (prefixWord ++ tailWord_2490738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490738).length < 2 ^ (prefixWord ++ tailWord_2490738).sum := by decide
  have hdescent : baseEnd_2490738 < baseStart_2490738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490741 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2490741 : Nat := 118140960795 + 2490741 * 2 ^ 59
def prefixEnd_2490741 : Nat := 4983230072969 + 3 ^ 40 * 2490741 * 2
def baseEnd_2490741 : Nat := 1278947318860344698082797

theorem tailTrace_2490741 : CollatzResearch.WordTrace tailWord_2490741 prefixEnd_2490741 1278947318860344698082797 := by
  unfold tailWord_2490741
  simp only [CollatzResearch.WordTrace]
  refine ⟨90844787469478216541304077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60563191646318811027536051 90844787469478216541304077)
  ·
    refine ⟨34066795301054331202989029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90844787469478216541304077 34066795301054331202989029)
    ·
      refine ⟨6387524118947687100560443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34066795301054331202989029 6387524118947687100560443)
      ·
        refine ⟨9581286178421530650840665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6387524118947687100560443 9581286178421530650840665)
        ·
          refine ⟨7185964633816147988130499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9581286178421530650840665 7185964633816147988130499)
          ·
            refine ⟨10778946950724221982195749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185964633816147988130499 10778946950724221982195749)
            ·
              refine ⟨2021052553260791621661703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10778946950724221982195749 2021052553260791621661703)
              ·
                refine ⟨3031578829891187432492555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021052553260791621661703 3031578829891187432492555)
                ·
                  refine ⟨4547368244836781148738833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031578829891187432492555 4547368244836781148738833)
                  ·
                    refine ⟨3410526183627585861554125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547368244836781148738833 3410526183627585861554125)
                    ·
                      refine ⟨1278947318860344698082797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410526183627585861554125 1278947318860344698082797)
                      ·
                        rfl

theorem cell23_2490741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2490741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490741 prefixEnd_2490741 := by exact prefixLift 2490741
  have htrace : WordTrace (prefixWord ++ tailWord_2490741) baseStart_2490741 baseEnd_2490741 := by
    simpa [prefixWord, tailWord_2490741, baseEnd_2490741] using wordTrace_append hprefix tailTrace_2490741
  have hstable : (prefixWord ++ tailWord_2490741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490741).length < 2 ^ (prefixWord ++ tailWord_2490741).sum := by decide
  have hdescent : baseEnd_2490741 < baseStart_2490741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490828 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2490828 : Nat := 118140960795 + 2490828 * 2 ^ 59
def prefixEnd_2490828 : Nat := 4983230072969 + 3 ^ 40 * 2490828 * 2
def baseEnd_2490828 : Nat := 1278991991677285857694897

theorem tailTrace_2490828 : CollatzResearch.WordTrace tailWord_2490828 prefixEnd_2490828 1278991991677285857694897 := by
  unfold tailWord_2490828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45423980310081515199860569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60565307080108686933147425 45423980310081515199860569)
  ·
    refine ⟨34067985232561136399895427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45423980310081515199860569 34067985232561136399895427)
    ·
      refine ⟨51101977848841704599843141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34067985232561136399895427 51101977848841704599843141)
      ·
        refine ⟨9581620846657819612470589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51101977848841704599843141 9581620846657819612470589)
        ·
          refine ⟨3593107817496682354676471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9581620846657819612470589 3593107817496682354676471)
          ·
            refine ⟨5389661726245023532014707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593107817496682354676471 5389661726245023532014707)
            ·
              refine ⟨8084492589367535298022061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389661726245023532014707 8084492589367535298022061)
              ·
                refine ⟨3031684721012825736758273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8084492589367535298022061 3031684721012825736758273)
                ·
                  refine ⟨2273763540759619302568705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3031684721012825736758273 2273763540759619302568705)
                  ·
                    refine ⟨1705322655569714476926529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2273763540759619302568705 1705322655569714476926529)
                    ·
                      refine ⟨1278991991677285857694897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705322655569714476926529 1278991991677285857694897)
                      ·
                        rfl

theorem cell23_2490828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2490828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490828 prefixEnd_2490828 := by exact prefixLift 2490828
  have htrace : WordTrace (prefixWord ++ tailWord_2490828) baseStart_2490828 baseEnd_2490828 := by
    simpa [prefixWord, tailWord_2490828, baseEnd_2490828] using wordTrace_append hprefix tailTrace_2490828
  have hstable : (prefixWord ++ tailWord_2490828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490828).length < 2 ^ (prefixWord ++ tailWord_2490828).sum := by decide
  have hdescent : baseEnd_2490828 < baseStart_2490828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490840 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2490840 : Nat := 118140960795 + 2490840 * 2 ^ 59
def prefixEnd_2490840 : Nat := 4983230072969 + 3 ^ 40 * 2490840 * 2
def baseEnd_2490840 : Nat := 1278998153445139810744841

theorem tailTrace_2490840 : CollatzResearch.WordTrace tailWord_2490840 prefixEnd_2490840 1278998153445139810744841 := by
  unfold tailWord_2490840
  simp only [CollatzResearch.WordTrace]
  refine ⟨45424199148059778224578987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60565598864079704299438649 45424199148059778224578987)
  ·
    refine ⟨68136298722089667336868481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45424199148059778224578987 68136298722089667336868481)
    ·
      refine ⟨51102224041567250502651361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68136298722089667336868481 51102224041567250502651361)
      ·
        refine ⟨38326668031175437876988521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51102224041567250502651361 38326668031175437876988521)
        ·
          refine ⟨28745001023381578407741391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38326668031175437876988521 28745001023381578407741391)
          ·
            refine ⟨43117501535072367611612087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28745001023381578407741391 43117501535072367611612087)
            ·
              refine ⟨64676252302608551417418131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43117501535072367611612087 64676252302608551417418131)
              ·
                refine ⟨97014378453912827126127197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64676252302608551417418131 97014378453912827126127197)
                ·
                  refine ⟨36380391920217310172297699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97014378453912827126127197 36380391920217310172297699)
                  ·
                    refine ⟨54570587880325965258446549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36380391920217310172297699 54570587880325965258446549)
                    ·
                      refine ⟨1278998153445139810744841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54570587880325965258446549 1278998153445139810744841)
                      ·
                        rfl

theorem cell23_2490840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2490840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490840 prefixEnd_2490840 := by exact prefixLift 2490840
  have htrace : WordTrace (prefixWord ++ tailWord_2490840) baseStart_2490840 baseEnd_2490840 := by
    simpa [prefixWord, tailWord_2490840, baseEnd_2490840] using wordTrace_append hprefix tailTrace_2490840
  have hstable : (prefixWord ++ tailWord_2490840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490840).length < 2 ^ (prefixWord ++ tailWord_2490840).sum := by decide
  have hdescent : baseEnd_2490840 < baseStart_2490840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490847 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 2, 5]
def baseStart_2490847 : Nat := 118140960795 + 2490847 * 2 ^ 59
def prefixEnd_2490847 : Nat := 4983230072969 + 3 ^ 40 * 2490847 * 2
def baseEnd_2490847 : Nat := 426333915936573761119103

theorem tailTrace_2490847 : CollatzResearch.WordTrace tailWord_2490847 prefixEnd_2490847 426333915936573761119103 := by
  unfold tailWord_2490847
  simp only [CollatzResearch.WordTrace]
  refine ⟨90848653607094196644662795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60565769071396131096441863 90848653607094196644662795)
  ·
    refine ⟨136272980410641294966994193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90848653607094196644662795 136272980410641294966994193)
    ·
      refine ⟨102204735307980971225245645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136272980410641294966994193 102204735307980971225245645)
      ·
        refine ⟨38326775740492864209467117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102204735307980971225245645 38326775740492864209467117)
        ·
          refine ⟨14372540902684824078550169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38326775740492864209467117 14372540902684824078550169)
          ·
            refine ⟨10779405677013618058912627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14372540902684824078550169 10779405677013618058912627)
            ·
              refine ⟨16169108515520427088368941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10779405677013618058912627 16169108515520427088368941)
              ·
                refine ⟨6063415693320160158138353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16169108515520427088368941 6063415693320160158138353)
                ·
                  refine ⟨4547561769990120118603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063415693320160158138353 4547561769990120118603765)
                  ·
                    refine ⟨426333915936573761119103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4547561769990120118603765 426333915936573761119103)
                    ·
                      rfl

theorem cell23_2490847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_2490847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490847 prefixEnd_2490847 := by exact prefixLift 2490847
  have htrace : WordTrace (prefixWord ++ tailWord_2490847) baseStart_2490847 baseEnd_2490847 := by
    simpa [prefixWord, tailWord_2490847, baseEnd_2490847] using wordTrace_append hprefix tailTrace_2490847
  have hstable : (prefixWord ++ tailWord_2490847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490847).length < 2 ^ (prefixWord ++ tailWord_2490847).sum := by decide
  have hdescent : baseEnd_2490847 < baseStart_2490847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490867 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4]
def baseStart_2490867 : Nat := 118140960795 + 2490867 * 2 ^ 59
def prefixEnd_2490867 : Nat := 4983230072969 + 3 ^ 40 * 2490867 * 2
def baseEnd_2490867 : Nat := 1279012017422811205107217

theorem tailTrace_2490867 : CollatzResearch.WordTrace tailWord_2490867 prefixEnd_2490867 1279012017422811205107217 := by
  unfold tailWord_2490867
  simp only [CollatzResearch.WordTrace]
  refine ⟨90849383067021740060390855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60566255378014493373593903 90849383067021740060390855)
  ·
    refine ⟨136274074600532610090586283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90849383067021740060390855 136274074600532610090586283)
    ·
      refine ⟨204411111900798915135879425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136274074600532610090586283 204411111900798915135879425)
      ·
        refine ⟨153308333925599186351909569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204411111900798915135879425 153308333925599186351909569)
        ·
          refine ⟨114981250444199389763932177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153308333925599186351909569 114981250444199389763932177)
          ·
            refine ⟨86235937833149542322949133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114981250444199389763932177 86235937833149542322949133)
            ·
              refine ⟨32338476687431078371105925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86235937833149542322949133 32338476687431078371105925)
              ·
                refine ⟨6063464378893327194582361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32338476687431078371105925 6063464378893327194582361)
                ·
                  refine ⟨4547598284169995395936771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063464378893327194582361 4547598284169995395936771)
                  ·
                    refine ⟨6821397426254993093905157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4547598284169995395936771 6821397426254993093905157)
                    ·
                      refine ⟨1279012017422811205107217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6821397426254993093905157 1279012017422811205107217)
                      ·
                        rfl

theorem cell23_2490867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_2490867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490867 prefixEnd_2490867 := by exact prefixLift 2490867
  have htrace : WordTrace (prefixWord ++ tailWord_2490867) baseStart_2490867 baseEnd_2490867 := by
    simpa [prefixWord, tailWord_2490867, baseEnd_2490867] using wordTrace_append hprefix tailTrace_2490867
  have hstable : (prefixWord ++ tailWord_2490867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490867).length < 2 ^ (prefixWord ++ tailWord_2490867).sum := by decide
  have hdescent : baseEnd_2490867 < baseStart_2490867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490894 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2490894 : Nat := 118140960795 + 2490894 * 2 ^ 59
def prefixEnd_2490894 : Nat := 4983230072969 + 3 ^ 40 * 2490894 * 2
def baseEnd_2490894 : Nat := 426341960466827533156531

theorem tailTrace_2490894 : CollatzResearch.WordTrace tailWord_2490894 prefixEnd_2490894 426341960466827533156531 := by
  unfold tailWord_2490894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356295979740490458952967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60566911891949282447749157 11356295979740490458952967)
  ·
    refine ⟨17034443969610735688429451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11356295979740490458952967 17034443969610735688429451)
    ·
      refine ⟨25551665954416103532644177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17034443969610735688429451 25551665954416103532644177)
      ·
        refine ⟨19163749465812077649483133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25551665954416103532644177 19163749465812077649483133)
        ·
          refine ⟨7186406049679529118556175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19163749465812077649483133 7186406049679529118556175)
          ·
            refine ⟨10779609074519293677834263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7186406049679529118556175 10779609074519293677834263)
            ·
              refine ⟨16169413611778940516751395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10779609074519293677834263 16169413611778940516751395)
              ·
                refine ⟨24254120417668410775127093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16169413611778940516751395 24254120417668410775127093)
                ·
                  refine ⟨2273823789156413510168165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24254120417668410775127093 2273823789156413510168165)
                  ·
                    refine ⟨426341960466827533156531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2273823789156413510168165 426341960466827533156531)
                    ·
                      rfl

theorem cell23_2490894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2490894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490894 prefixEnd_2490894 := by exact prefixLift 2490894
  have htrace : WordTrace (prefixWord ++ tailWord_2490894) baseStart_2490894 baseEnd_2490894 := by
    simpa [prefixWord, tailWord_2490894, baseEnd_2490894] using wordTrace_append hprefix tailTrace_2490894
  have hstable : (prefixWord ++ tailWord_2490894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490894).length < 2 ^ (prefixWord ++ tailWord_2490894).sum := by decide
  have hdescent : baseEnd_2490894 < baseStart_2490894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490904 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2490904 : Nat := 118140960795 + 2490904 * 2 ^ 59
def prefixEnd_2490904 : Nat := 4983230072969 + 3 ^ 40 * 2490904 * 2
def baseEnd_2490904 : Nat := 1279031016207027560344547

theorem tailTrace_2490904 : CollatzResearch.WordTrace tailWord_2490904 prefixEnd_2490904 1279031016207027560344547 := by
  unfold tailWord_2490904
  simp only [CollatzResearch.WordTrace]
  refine ⟨45425366283943847689743883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60567155045258463586325177 45425366283943847689743883)
  ·
    refine ⟨68138049425915771534615825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45425366283943847689743883 68138049425915771534615825)
    ·
      refine ⟨51103537069436828650961869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68138049425915771534615825 51103537069436828650961869)
      ·
        refine ⟨19163826401038810744110701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51103537069436828650961869 19163826401038810744110701)
        ·
          refine ⟨7186434900389554029041513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19163826401038810744110701 7186434900389554029041513)
          ·
            refine ⟨5389826175292165521781135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7186434900389554029041513 5389826175292165521781135)
            ·
              refine ⟨8084739262938248282671703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389826175292165521781135 8084739262938248282671703)
              ·
                refine ⟨12127108894407372424007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8084739262938248282671703 12127108894407372424007555)
                ·
                  refine ⟨18190663341611058636011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12127108894407372424007555 18190663341611058636011333)
                  ·
                    refine ⟨3410749376552073494252125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18190663341611058636011333 3410749376552073494252125)
                    ·
                      refine ⟨1279031016207027560344547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410749376552073494252125 1279031016207027560344547)
                      ·
                        rfl

theorem cell23_2490904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2490904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490904 prefixEnd_2490904 := by exact prefixLift 2490904
  have htrace : WordTrace (prefixWord ++ tailWord_2490904) baseStart_2490904 baseEnd_2490904 := by
    simpa [prefixWord, tailWord_2490904, baseEnd_2490904] using wordTrace_append hprefix tailTrace_2490904
  have hstable : (prefixWord ++ tailWord_2490904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490904).length < 2 ^ (prefixWord ++ tailWord_2490904).sum := by decide
  have hdescent : baseEnd_2490904 < baseStart_2490904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490941 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 6]
def baseStart_2490941 : Nat := 118140960795 + 2490941 * 2 ^ 59
def prefixEnd_2490941 : Nat := 4983230072969 + 3 ^ 40 * 2490941 * 2
def baseEnd_2490941 : Nat := 142116668332360435064653

theorem tailTrace_2490941 : CollatzResearch.WordTrace tailWord_2490941 prefixEnd_2490941 142116668332360435064653 := by
  unfold tailWord_2490941
  simp only [CollatzResearch.WordTrace]
  refine ⟨90852082068753650698584677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60568054712502433799056451 90852082068753650698584677)
  ·
    refine ⟨17034765387891309505984627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90852082068753650698584677 17034765387891309505984627)
    ·
      refine ⟨25552148081836964258976941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17034765387891309505984627 25552148081836964258976941)
      ·
        refine ⟨9582055530688861597116353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25552148081836964258976941 9582055530688861597116353)
        ·
          refine ⟨7186541648016646197837265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9582055530688861597116353 7186541648016646197837265)
          ·
            refine ⟨5389906236012484648377949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7186541648016646197837265 5389906236012484648377949)
            ·
              refine ⟨2021214838504681743141731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5389906236012484648377949 2021214838504681743141731)
              ·
                refine ⟨3031822257757022614712597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021214838504681743141731 3031822257757022614712597)
                ·
                  refine ⟨142116668332360435064653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3031822257757022614712597 142116668332360435064653)
                  ·
                    rfl

theorem cell23_2490941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_2490941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490941 prefixEnd_2490941 := by exact prefixLift 2490941
  have htrace : WordTrace (prefixWord ++ tailWord_2490941) baseStart_2490941 baseEnd_2490941 := by
    simpa [prefixWord, tailWord_2490941, baseEnd_2490941] using wordTrace_append hprefix tailTrace_2490941
  have hstable : (prefixWord ++ tailWord_2490941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490941).length < 2 ^ (prefixWord ++ tailWord_2490941).sum := by decide
  have hdescent : baseEnd_2490941 < baseStart_2490941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490944 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2]
def baseStart_2490944 : Nat := 118140960795 + 2490944 * 2 ^ 59
def prefixEnd_2490944 : Nat := 4983230072969 + 3 ^ 40 * 2490944 * 2
def baseEnd_2490944 : Nat := 1279051555433207403844363

theorem tailTrace_2490944 : CollatzResearch.WordTrace tailWord_2490944 prefixEnd_2490944 1279051555433207403844363 := by
  unfold tailWord_2490944
  simp only [CollatzResearch.WordTrace]
  refine ⟨45426095743871391105471943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60568127658495188140629257 45426095743871391105471943)
  ·
    refine ⟨68139143615807086658207915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45426095743871391105471943 68139143615807086658207915)
    ·
      refine ⟨102208715423710629987311873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68139143615807086658207915 102208715423710629987311873)
      ·
        refine ⟨76656536567782972490483905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102208715423710629987311873 76656536567782972490483905)
        ·
          refine ⟨57492402425837229367862929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76656536567782972490483905 57492402425837229367862929)
          ·
            refine ⟨43119301819377922025897197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57492402425837229367862929 43119301819377922025897197)
            ·
              refine ⟨16169738182266720759711449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43119301819377922025897197 16169738182266720759711449)
              ·
                refine ⟨12127303636700040569783587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16169738182266720759711449 12127303636700040569783587)
                ·
                  refine ⟨18190955455050060854675381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12127303636700040569783587 18190955455050060854675381)
                  ·
                    refine ⟨1705402073910943205125817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18190955455050060854675381 1705402073910943205125817)
                    ·
                      refine ⟨1279051555433207403844363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705402073910943205125817 1279051555433207403844363)
                      ·
                        rfl

theorem cell23_2490944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_2490944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490944 prefixEnd_2490944 := by exact prefixLift 2490944
  have htrace : WordTrace (prefixWord ++ tailWord_2490944) baseStart_2490944 baseEnd_2490944 := by
    simpa [prefixWord, tailWord_2490944, baseEnd_2490944] using wordTrace_append hprefix tailTrace_2490944
  have hstable : (prefixWord ++ tailWord_2490944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490944).length < 2 ^ (prefixWord ++ tailWord_2490944).sum := by decide
  have hdescent : baseEnd_2490944 < baseStart_2490944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490951 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_2490951 : Nat := 118140960795 + 2490951 * 2 ^ 59
def prefixEnd_2490951 : Nat := 4983230072969 + 3 ^ 40 * 2490951 * 2
def baseEnd_2490951 : Nat := 1279055149797788876456831

theorem tailTrace_2490951 : CollatzResearch.WordTrace tailWord_2490951 prefixEnd_2490951 1279055149797788876456831 := by
  unfold tailWord_2490951
  simp only [CollatzResearch.WordTrace]
  refine ⟨90852446798717422406448707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60568297865811614937632471 90852446798717422406448707)
  ·
    refine ⟨136278670198076133609673061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90852446798717422406448707 136278670198076133609673061)
    ·
      refine ⟨25552250662139275051813699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136278670198076133609673061 25552250662139275051813699)
      ·
        refine ⟨38328375993208912577720549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25552250662139275051813699 38328375993208912577720549)
        ·
          refine ⟨7186570498726671108322603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38328375993208912577720549 7186570498726671108322603)
          ·
            refine ⟨10779855748090006662483905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7186570498726671108322603 10779855748090006662483905)
            ·
              refine ⟨8084891811067504996862929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10779855748090006662483905 8084891811067504996862929)
              ·
                refine ⟨6063668858300628747647197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8084891811067504996862929 6063668858300628747647197)
                ·
                  refine ⟨2273875821862735780367699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6063668858300628747647197 2273875821862735780367699)
                  ·
                    refine ⟨3410813732794103670551549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2273875821862735780367699 3410813732794103670551549)
                    ·
                      refine ⟨1279055149797788876456831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410813732794103670551549 1279055149797788876456831)
                      ·
                        rfl

theorem cell23_2490951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_2490951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490951 prefixEnd_2490951 := by exact prefixLift 2490951
  have htrace : WordTrace (prefixWord ++ tailWord_2490951) baseStart_2490951 baseEnd_2490951 := by
    simpa [prefixWord, tailWord_2490951, baseEnd_2490951] using wordTrace_append hprefix tailTrace_2490951
  have hstable : (prefixWord ++ tailWord_2490951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490951).length < 2 ^ (prefixWord ++ tailWord_2490951).sum := by decide
  have hdescent : baseEnd_2490951 < baseStart_2490951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490954 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_2490954 : Nat := 118140960795 + 2490954 * 2 ^ 59
def prefixEnd_2490954 : Nat := 4983230072969 + 3 ^ 40 * 2490954 * 2
def baseEnd_2490954 : Nat := 426352230079917454906439

theorem tailTrace_2490954 : CollatzResearch.WordTrace tailWord_2490954 prefixEnd_2490954 426352230079917454906439 := by
  unfold tailWord_2490954
  simp only [CollatzResearch.WordTrace]
  refine ⟨22713139054426638479701979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60568370811804369279205277 22713139054426638479701979)
  ·
    refine ⟨34069708581639957719552969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22713139054426638479701979 34069708581639957719552969)
    ·
      refine ⟨25552281436229968289664727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34069708581639957719552969 25552281436229968289664727)
      ·
        refine ⟨38328422154344952434497091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25552281436229968289664727 38328422154344952434497091)
        ·
          refine ⟨57492633231517428651745637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38328422154344952434497091 57492633231517428651745637)
          ·
            refine ⟨10779868730909517872202307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57492633231517428651745637 10779868730909517872202307)
            ·
              refine ⟨16169803096364276808303461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10779868730909517872202307 16169803096364276808303461)
              ·
                refine ⟨3031838080568301901556899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16169803096364276808303461 3031838080568301901556899)
                ·
                  refine ⟨4547757120852452852335349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031838080568301901556899 4547757120852452852335349)
                  ·
                    refine ⟨426352230079917454906439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4547757120852452852335349 426352230079917454906439)
                    ·
                      rfl

theorem cell23_2490954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_2490954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490954 prefixEnd_2490954 := by exact prefixLift 2490954
  have htrace : WordTrace (prefixWord ++ tailWord_2490954) baseStart_2490954 baseEnd_2490954 := by
    simpa [prefixWord, tailWord_2490954, baseEnd_2490954] using wordTrace_append hprefix tailTrace_2490954
  have hstable : (prefixWord ++ tailWord_2490954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490954).length < 2 ^ (prefixWord ++ tailWord_2490954).sum := by decide
  have hdescent : baseEnd_2490954 < baseStart_2490954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490967 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 3, 6]
def baseStart_2490967 : Nat := 118140960795 + 2490967 * 2 ^ 59
def prefixEnd_2490967 : Nat := 4983230072969 + 3 ^ 40 * 2490967 * 2
def baseEnd_2490967 : Nat := 426354455162753604618919

theorem tailTrace_2490967 : CollatzResearch.WordTrace tailWord_2490967 prefixEnd_2490967 426354455162753604618919 := by
  unfold tailWord_2490967
  simp only [CollatzResearch.WordTrace]
  refine ⟨90853030366659457139031155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60568686911106304759354103 90853030366659457139031155)
  ·
    refine ⟨136279545549989185708546733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90853030366659457139031155 136279545549989185708546733)
    ·
      refine ⟨51104829581245944640705025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136279545549989185708546733 51104829581245944640705025)
      ·
        refine ⟨38328622185934458480528769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51104829581245944640705025 38328622185934458480528769)
        ·
          refine ⟨28746466639450843860396577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38328622185934458480528769 28746466639450843860396577)
          ·
            refine ⟨21559849979588132895297433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28746466639450843860396577 21559849979588132895297433)
            ·
              refine ⟨16169887484691099671473075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21559849979588132895297433 16169887484691099671473075)
              ·
                refine ⟨24254831227036649507209613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16169887484691099671473075 24254831227036649507209613)
                ·
                  refine ⟨9095561710138743565203605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24254831227036649507209613 9095561710138743565203605)
                  ·
                    refine ⟨426354455162753604618919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9095561710138743565203605 426354455162753604618919)
                    ·
                      rfl

theorem cell23_2490967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_2490967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490967 prefixEnd_2490967 := by exact prefixLift 2490967
  have htrace : WordTrace (prefixWord ++ tailWord_2490967) baseStart_2490967 baseEnd_2490967 := by
    simpa [prefixWord, tailWord_2490967, baseEnd_2490967] using wordTrace_append hprefix tailTrace_2490967
  have hstable : (prefixWord ++ tailWord_2490967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490967).length < 2 ^ (prefixWord ++ tailWord_2490967).sum := by decide
  have hdescent : baseEnd_2490967 < baseStart_2490967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490968 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 1, 1, 3]
def baseStart_2490968 : Nat := 118140960795 + 2490968 * 2 ^ 59
def prefixEnd_2490968 : Nat := 4983230072969 + 3 ^ 40 * 2490968 * 2
def baseEnd_2490968 : Nat := 1279063878968915309944253

theorem tailTrace_2490968 : CollatzResearch.WordTrace tailWord_2490968 prefixEnd_2490968 1279063878968915309944253 := by
  unfold tailWord_2490968
  simp only [CollatzResearch.WordTrace]
  refine ⟨45426533419827917154908779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60568711226437222873211705 45426533419827917154908779)
  ·
    refine ⟨68139800129741875732363169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45426533419827917154908779 68139800129741875732363169)
    ·
      refine ⟨51104850097306406799272377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68139800129741875732363169 51104850097306406799272377)
      ·
        refine ⟨38328637572979805099454283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51104850097306406799272377 38328637572979805099454283)
        ·
          refine ⟨57492956359469707649181425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38328637572979805099454283 57492956359469707649181425)
          ·
            refine ⟨43119717269602280736886069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57492956359469707649181425 43119717269602280736886069)
            ·
              refine ⟨4042473494025213819083069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43119717269602280736886069 4042473494025213819083069)
              ·
                refine ⟨1515927560259455182156151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4042473494025213819083069 1515927560259455182156151)
                ·
                  refine ⟨2273891340389182773234227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515927560259455182156151 2273891340389182773234227)
                  ·
                    refine ⟨3410837010583774159851341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2273891340389182773234227 3410837010583774159851341)
                    ·
                      refine ⟨1279063878968915309944253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410837010583774159851341 1279063878968915309944253)
                      ·
                        rfl

theorem cell23_2490968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_2490968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490968 prefixEnd_2490968 := by exact prefixLift 2490968
  have htrace : WordTrace (prefixWord ++ tailWord_2490968) baseStart_2490968 baseEnd_2490968 := by
    simpa [prefixWord, tailWord_2490968, baseEnd_2490968] using wordTrace_append hprefix tailTrace_2490968
  have hstable : (prefixWord ++ tailWord_2490968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490968).length < 2 ^ (prefixWord ++ tailWord_2490968).sum := by decide
  have hdescent : baseEnd_2490968 < baseStart_2490968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2490987 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_2490987 : Nat := 118140960795 + 2490987 * 2 ^ 59
def prefixEnd_2490987 : Nat := 4983230072969 + 3 ^ 40 * 2490987 * 2
def baseEnd_2490987 : Nat := 1279073635101350735606665

theorem tailTrace_2490987 : CollatzResearch.WordTrace tailWord_2490987 prefixEnd_2490987 1279073635101350735606665 := by
  unfold tailWord_2490987
  simp only [CollatzResearch.WordTrace]
  refine ⟨90853759826587000554759215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60569173217724667036506143 90853759826587000554759215)
  ·
    refine ⟨136280639739880500832138823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90853759826587000554759215 136280639739880500832138823)
    ·
      refine ⟨204420959609820751248208235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136280639739880500832138823 204420959609820751248208235)
      ·
        refine ⟨306631439414731126872312353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204420959609820751248208235 306631439414731126872312353)
        ·
          refine ⟨229973579561048345154234265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306631439414731126872312353 229973579561048345154234265)
          ·
            refine ⟨172480184670786258865675699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229973579561048345154234265 172480184670786258865675699)
            ·
              refine ⟨258720277006179388298513549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172480184670786258865675699 258720277006179388298513549)
              ·
                refine ⟨97020103877317270611942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258720277006179388298513549 97020103877317270611942581)
                ·
                  refine ⟨9095634738498494119869617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97020103877317270611942581 9095634738498494119869617)
                  ·
                    refine ⟨6821726053873870589902213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9095634738498494119869617 6821726053873870589902213)
                    ·
                      refine ⟨1279073635101350735606665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6821726053873870589902213 1279073635101350735606665)
                      ·
                        rfl

theorem cell23_2490987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_2490987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2490987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2490987 prefixEnd_2490987 := by exact prefixLift 2490987
  have htrace : WordTrace (prefixWord ++ tailWord_2490987) baseStart_2490987 baseEnd_2490987 := by
    simpa [prefixWord, tailWord_2490987, baseEnd_2490987] using wordTrace_append hprefix tailTrace_2490987
  have hstable : (prefixWord ++ tailWord_2490987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2490987).length < 2 ^ (prefixWord ++ tailWord_2490987).sum := by decide
  have hdescent : baseEnd_2490987 < baseStart_2490987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2490987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491001 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_2491001 : Nat := 118140960795 + 2491001 * 2 ^ 59
def prefixEnd_2491001 : Nat := 4983230072969 + 3 ^ 40 * 2491001 * 2
def baseEnd_2491001 : Nat := 426360274610171226943867

theorem tailTrace_2491001 : CollatzResearch.WordTrace tailWord_2491001 prefixEnd_2491001 426360274610171226943867 := by
  unfold tailWord_2491001
  simp only [CollatzResearch.WordTrace]
  refine ⟨90854270448536280945768857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60569513632357520630512571 90854270448536280945768857)
  ·
    refine ⟨68140702836402210709326643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90854270448536280945768857 68140702836402210709326643)
    ·
      refine ⟨102211054254603316063989965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68140702836402210709326643 102211054254603316063989965)
      ·
        refine ⟨38329145345476243523996237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102211054254603316063989965 38329145345476243523996237)
        ·
          refine ⟨14373429504553591321498589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38329145345476243523996237 14373429504553591321498589)
          ·
            refine ⟨5390036064207596745561971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14373429504553591321498589 5390036064207596745561971)
            ·
              refine ⟨8085054096311395118342957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5390036064207596745561971 8085054096311395118342957)
              ·
                refine ⟨3031895286116773169378609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8085054096311395118342957 3031895286116773169378609)
                ·
                  refine ⟨2273921464587579877033957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3031895286116773169378609 2273921464587579877033957)
                  ·
                    refine ⟨426360274610171226943867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2273921464587579877033957 426360274610171226943867)
                    ·
                      rfl

theorem cell23_2491001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_2491001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491001 prefixEnd_2491001 := by exact prefixLift 2491001
  have htrace : WordTrace (prefixWord ++ tailWord_2491001) baseStart_2491001 baseEnd_2491001 := by
    simpa [prefixWord, tailWord_2491001, baseEnd_2491001] using wordTrace_append hprefix tailTrace_2491001
  have hstable : (prefixWord ++ tailWord_2491001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491001).length < 2 ^ (prefixWord ++ tailWord_2491001).sum := by decide
  have hdescent : baseEnd_2491001 < baseStart_2491001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491011 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 3]
def baseStart_2491011 : Nat := 118140960795 + 2491011 * 2 ^ 59
def prefixEnd_2491011 : Nat := 4983230072969 + 3 ^ 40 * 2491011 * 2
def baseEnd_2491011 : Nat := 1279085958637058641706555

theorem tailTrace_2491011 : CollatzResearch.WordTrace tailWord_2491011 prefixEnd_2491011 1279085958637058641706555 := by
  unfold tailWord_2491011
  simp only [CollatzResearch.WordTrace]
  refine ⟨90854635178500052653632887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60569756785666701769088591 90854635178500052653632887)
  ·
    refine ⟨136281952767750078980449331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90854635178500052653632887 136281952767750078980449331)
    ·
      refine ⟨204422929151625118470673997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136281952767750078980449331 204422929151625118470673997)
      ·
        refine ⟨76658598431859419426502749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204422929151625118470673997 76658598431859419426502749)
        ·
          refine ⟨28746974411947282284938531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76658598431859419426502749 28746974411947282284938531)
          ·
            refine ⟨43120461617920923427407797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28746974411947282284938531 43120461617920923427407797)
            ·
              refine ⟨4042543276680086571319481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43120461617920923427407797 4042543276680086571319481)
              ·
                refine ⟨3031907457510064928489611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042543276680086571319481 3031907457510064928489611)
                ·
                  refine ⟨4547861186265097392734417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031907457510064928489611 4547861186265097392734417)
                  ·
                    refine ⟨3410895889698823044550813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4547861186265097392734417 3410895889698823044550813)
                    ·
                      refine ⟨1279085958637058641706555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3410895889698823044550813 1279085958637058641706555)
                      ·
                        rfl

theorem cell23_2491011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_2491011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491011 prefixEnd_2491011 := by exact prefixLift 2491011
  have htrace : WordTrace (prefixWord ++ tailWord_2491011) baseStart_2491011 baseEnd_2491011 := by
    simpa [prefixWord, tailWord_2491011, baseEnd_2491011] using wordTrace_append hprefix tailTrace_2491011
  have hstable : (prefixWord ++ tailWord_2491011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491011).length < 2 ^ (prefixWord ++ tailWord_2491011).sum := by decide
  have hdescent : baseEnd_2491011 < baseStart_2491011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491028 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2491028 : Nat := 118140960795 + 2491028 * 2 ^ 59
def prefixEnd_2491028 : Nat := 4983230072969 + 3 ^ 40 * 2491028 * 2
def baseEnd_2491028 : Nat := 1279094687808185075193977

theorem tailTrace_2491028 : CollatzResearch.WordTrace tailWord_2491028 prefixEnd_2491028 1279094687808185075193977 := by
  unfold tailWord_2491028
  simp only [CollatzResearch.WordTrace]
  refine ⟨45427627609719232278500869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60570170146292309704667825 45427627609719232278500869)
  ·
    refine ⟨8517680176822356052218913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45427627609719232278500869 8517680176822356052218913)
    ·
      refine ⟨6388260132616767039164185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8517680176822356052218913 6388260132616767039164185)
      ·
        refine ⟨4791195099462575279373139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6388260132616767039164185 4791195099462575279373139)
        ·
          refine ⟨7186792649193862919059709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791195099462575279373139 7186792649193862919059709)
          ·
            refine ⟨2695047243447698594647391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7186792649193862919059709 2695047243447698594647391)
            ·
              refine ⟨4042570865171547891971087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695047243447698594647391 4042570865171547891971087)
              ·
                refine ⟨6063856297757321837956631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4042570865171547891971087 6063856297757321837956631)
                ·
                  refine ⟨9095784446635982756934947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063856297757321837956631 9095784446635982756934947)
                  ·
                    refine ⟨13643676669953974135402421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9095784446635982756934947 13643676669953974135402421)
                    ·
                      refine ⟨1279094687808185075193977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13643676669953974135402421 1279094687808185075193977)
                      ·
                        rfl

theorem cell23_2491028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2491028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491028 prefixEnd_2491028 := by exact prefixLift 2491028
  have htrace : WordTrace (prefixWord ++ tailWord_2491028) baseStart_2491028 baseEnd_2491028 := by
    simpa [prefixWord, tailWord_2491028, baseEnd_2491028] using wordTrace_append hprefix tailTrace_2491028
  have hstable : (prefixWord ++ tailWord_2491028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491028).length < 2 ^ (prefixWord ++ tailWord_2491028).sum := by decide
  have hdescent : baseEnd_2491028 < baseStart_2491028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491068 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_2491068 : Nat := 118140960795 + 2491068 * 2 ^ 59
def prefixEnd_2491068 : Nat := 4983230072969 + 3 ^ 40 * 2491068 * 2
def baseEnd_2491068 : Nat := 1279115227034364918693793

theorem tailTrace_2491068 : CollatzResearch.WordTrace tailWord_2491068 prefixEnd_2491068 1279115227034364918693793 := by
  unfold tailWord_2491068
  simp only [CollatzResearch.WordTrace]
  refine ⟨45428357069646775694228929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60571142759529034258971905 45428357069646775694228929)
  ·
    refine ⟨34071267802235081770671697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45428357069646775694228929 34071267802235081770671697)
    ·
      refine ⟨25553450851676311328003773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34071267802235081770671697 25553450851676311328003773)
      ·
        refine ⟨9582544069378616748001415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25553450851676311328003773 9582544069378616748001415)
        ·
          refine ⟨14373816104067925122002123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582544069378616748001415 14373816104067925122002123)
          ·
            refine ⟨21560724156101887683003185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14373816104067925122002123 21560724156101887683003185)
            ·
              refine ⟨16170543117076415762252389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21560724156101887683003185 16170543117076415762252389)
              ·
                refine ⟨3031976834451827955422323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16170543117076415762252389 3031976834451827955422323)
                ·
                  refine ⟨4547965251677741933133485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3031976834451827955422323 4547965251677741933133485)
                  ·
                    refine ⟨1705486969379153224925057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4547965251677741933133485 1705486969379153224925057)
                    ·
                      refine ⟨1279115227034364918693793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705486969379153224925057 1279115227034364918693793)
                      ·
                        rfl

theorem cell23_2491068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_2491068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491068 prefixEnd_2491068 := by exact prefixLift 2491068
  have htrace : WordTrace (prefixWord ++ tailWord_2491068) baseStart_2491068 baseEnd_2491068 := by
    simpa [prefixWord, tailWord_2491068, baseEnd_2491068] using wordTrace_append hprefix tailTrace_2491068
  have hstable : (prefixWord ++ tailWord_2491068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491068).length < 2 ^ (prefixWord ++ tailWord_2491068).sum := by decide
  have hdescent : baseEnd_2491068 < baseStart_2491068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491092 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2491092 : Nat := 118140960795 + 2491092 * 2 ^ 59
def prefixEnd_2491092 : Nat := 4983230072969 + 3 ^ 40 * 2491092 * 2
def baseEnd_2491092 : Nat := 1279127550570072824793683

theorem tailTrace_2491092 : CollatzResearch.WordTrace tailWord_2491092 prefixEnd_2491092 1279127550570072824793683 := by
  unfold tailWord_2491092
  simp only [CollatzResearch.WordTrace]
  refine ⟨45428794745603301743665765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60571726327471068991554353 45428794745603301743665765)
  ·
    refine ⟨8517899014800619076937331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45428794745603301743665765 8517899014800619076937331)
    ·
      refine ⟨12776848522200928615405997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8517899014800619076937331 12776848522200928615405997)
      ·
        refine ⟨4791318195825348230777249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12776848522200928615405997 4791318195825348230777249)
        ·
          refine ⟨3593488646869011173082937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4791318195825348230777249 3593488646869011173082937)
          ·
            refine ⟨2695116485151758379812203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3593488646869011173082937 2695116485151758379812203)
            ·
              refine ⟨4042674727727637569718305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695116485151758379812203 4042674727727637569718305)
              ·
                refine ⟨3032006045795728177288729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042674727727637569718305 3032006045795728177288729)
                ·
                  refine ⟨2274004534346796132966547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032006045795728177288729 2274004534346796132966547)
                  ·
                    refine ⟨3411006801520194199449821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2274004534346796132966547 3411006801520194199449821)
                    ·
                      refine ⟨1279127550570072824793683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411006801520194199449821 1279127550570072824793683)
                      ·
                        rfl

theorem cell23_2491092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2491092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491092 prefixEnd_2491092 := by exact prefixLift 2491092
  have htrace : WordTrace (prefixWord ++ tailWord_2491092) baseStart_2491092 baseEnd_2491092 := by
    simpa [prefixWord, tailWord_2491092, baseEnd_2491092] using wordTrace_append hprefix tailTrace_2491092
  have hstable : (prefixWord ++ tailWord_2491092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491092).length < 2 ^ (prefixWord ++ tailWord_2491092).sum := by decide
  have hdescent : baseEnd_2491092 < baseStart_2491092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491098 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_2491098 : Nat := 118140960795 + 2491098 * 2 ^ 59
def prefixEnd_2491098 : Nat := 4983230072969 + 3 ^ 40 * 2491098 * 2
def baseEnd_2491098 : Nat := 1279130631453999801318655

theorem tailTrace_2491098 : CollatzResearch.WordTrace tailWord_2491098 prefixEnd_2491098 1279130631453999801318655 := by
  unfold tailWord_2491098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22714452082296216628012487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60571872219456577674699965 22714452082296216628012487)
  ·
    refine ⟨34071678123444324942018731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22714452082296216628012487 34071678123444324942018731)
    ·
      refine ⟨51107517185166487413028097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34071678123444324942018731 51107517185166487413028097)
      ·
        refine ⟨38330637888874865559771073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51107517185166487413028097 38330637888874865559771073)
        ·
          refine ⟨28747978416656149169828305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38330637888874865559771073 28747978416656149169828305)
          ·
            refine ⟨21560983812492111877371229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28747978416656149169828305 21560983812492111877371229)
            ·
              refine ⟨8085368929684541954014211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21560983812492111877371229 8085368929684541954014211)
              ·
                refine ⟨12128053394526812931021317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8085368929684541954014211 12128053394526812931021317)
                ·
                  refine ⟨2274010011473777424566497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12128053394526812931021317 2274010011473777424566497)
                  ·
                    refine ⟨1705507508605333068424873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2274010011473777424566497 1705507508605333068424873)
                    ·
                      refine ⟨1279130631453999801318655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705507508605333068424873 1279130631453999801318655)
                      ·
                        rfl

theorem cell23_2491098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_2491098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491098 prefixEnd_2491098 := by exact prefixLift 2491098
  have htrace : WordTrace (prefixWord ++ tailWord_2491098) baseStart_2491098 baseEnd_2491098 := by
    simpa [prefixWord, tailWord_2491098, baseEnd_2491098] using wordTrace_append hprefix tailTrace_2491098
  have hstable : (prefixWord ++ tailWord_2491098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491098).length < 2 ^ (prefixWord ++ tailWord_2491098).sum := by decide
  have hdescent : baseEnd_2491098 < baseStart_2491098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491171 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 6, 2]
def baseStart_2491171 : Nat := 118140960795 + 2491171 * 2 ^ 59
def prefixEnd_2491171 : Nat := 4983230072969 + 3 ^ 40 * 2491171 * 2
def baseEnd_2491171 : Nat := 1279168115541778015705819

theorem tailTrace_2491171 : CollatzResearch.WordTrace tailWord_2491171 prefixEnd_2491171 1279168115541778015705819 := by
  unfold tailWord_2491171
  simp only [CollatzResearch.WordTrace]
  refine ⟨90860470857920399979457367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60573647238613599986304911 90860470857920399979457367)
  ·
    refine ⟨136290706286880599969186051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90860470857920399979457367 136290706286880599969186051)
    ·
      refine ⟨204436059430320899953779077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136290706286880599969186051 204436059430320899953779077)
      ·
        refine ⟨38331761143185168741333577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204436059430320899953779077 38331761143185168741333577)
        ·
          refine ⟨28748820857388876556000183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38331761143185168741333577 28748820857388876556000183)
          ·
            refine ⟨43123231286083314834000275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28748820857388876556000183 43123231286083314834000275)
            ·
              refine ⟨64684846929124972251000413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43123231286083314834000275 64684846929124972251000413)
              ·
                refine ⟨24256817598421864594125155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64684846929124972251000413 24256817598421864594125155)
                ·
                  refine ⟨36385226397632796891187733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24256817598421864594125155 36385226397632796891187733)
                  ·
                    refine ⟨1705557487389037354274425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36385226397632796891187733 1705557487389037354274425)
                    ·
                      refine ⟨1279168115541778015705819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705557487389037354274425 1279168115541778015705819)
                      ·
                        rfl

theorem cell23_2491171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_2491171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491171 prefixEnd_2491171 := by exact prefixLift 2491171
  have htrace : WordTrace (prefixWord ++ tailWord_2491171) baseStart_2491171 baseEnd_2491171 := by
    simpa [prefixWord, tailWord_2491171, baseEnd_2491171] using wordTrace_append hprefix tailTrace_2491171
  have hstable : (prefixWord ++ tailWord_2491171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491171).length < 2 ^ (prefixWord ++ tailWord_2491171).sum := by decide
  have hdescent : baseEnd_2491171 < baseStart_2491171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491184 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_2491184 : Nat := 118140960795 + 2491184 * 2 ^ 59
def prefixEnd_2491184 : Nat := 4983230072969 + 3 ^ 40 * 2491184 * 2
def baseEnd_2491184 : Nat := 1279174790790286464843259

theorem tailTrace_2491184 : CollatzResearch.WordTrace tailWord_2491184 prefixEnd_2491184 1279174790790286464843259 := by
  unfold tailWord_2491184
  simp only [CollatzResearch.WordTrace]
  refine ⟨45430472503436651599840303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60573963337915535466453737 45430472503436651599840303)
  ·
    refine ⟨68145708755154977399760455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45430472503436651599840303 68145708755154977399760455)
    ·
      refine ⟨102218563132732466099640683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68145708755154977399760455 102218563132732466099640683)
      ·
        refine ⟨153327844699098699149461025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102218563132732466099640683 153327844699098699149461025)
        ·
          refine ⟨114995883524324024362095769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153327844699098699149461025 114995883524324024362095769)
          ·
            refine ⟨86246912643243018271571827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114995883524324024362095769 86246912643243018271571827)
            ·
              refine ⟨129370368964864527407357741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86246912643243018271571827 129370368964864527407357741)
              ·
                refine ⟨48513888361824197777759153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129370368964864527407357741 48513888361824197777759153)
                ·
                  refine ⟨36385416271368148333319365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48513888361824197777759153 36385416271368148333319365)
                  ·
                    refine ⟨6822265550881527812497381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36385416271368148333319365 6822265550881527812497381)
                    ·
                      refine ⟨1279174790790286464843259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6822265550881527812497381 1279174790790286464843259)
                      ·
                        rfl

theorem cell23_2491184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_2491184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491184 prefixEnd_2491184 := by exact prefixLift 2491184
  have htrace : WordTrace (prefixWord ++ tailWord_2491184) baseStart_2491184 baseEnd_2491184 := by
    simpa [prefixWord, tailWord_2491184, baseEnd_2491184] using wordTrace_append hprefix tailTrace_2491184
  have hstable : (prefixWord ++ tailWord_2491184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491184).length < 2 ^ (prefixWord ++ tailWord_2491184).sum := by decide
  have hdescent : baseEnd_2491184 < baseStart_2491184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491206 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2491206 : Nat := 118140960795 + 2491206 * 2 ^ 59
def prefixEnd_2491206 : Nat := 4983230072969 + 3 ^ 40 * 2491206 * 2
def baseEnd_2491206 : Nat := 142131787484965042085351

theorem tailTrace_2491206 : CollatzResearch.WordTrace tailWord_2491206 prefixEnd_2491206 142131787484965042085351 := by
  unfold tailWord_2491206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839429606649800029905671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60574498275195733971320981 2839429606649800029905671)
  ·
    refine ⟨4259144409974700044858507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839429606649800029905671 4259144409974700044858507)
    ·
      refine ⟨6388716614962050067287761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259144409974700044858507 6388716614962050067287761)
      ·
        refine ⟨4791537461221537550465821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6388716614962050067287761 4791537461221537550465821)
        ·
          refine ⟨1796826547958076581424683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4791537461221537550465821 1796826547958076581424683)
          ·
            refine ⟨2695239821937114872137025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796826547958076581424683 2695239821937114872137025)
            ·
              refine ⟨2021429866452836154102769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2695239821937114872137025 2021429866452836154102769)
              ·
                refine ⟨1516072399839627115577077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021429866452836154102769 1516072399839627115577077)
                ·
                  refine ⟨142131787484965042085351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516072399839627115577077 142131787484965042085351)
                  ·
                    rfl

theorem cell23_2491206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2491206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491206 prefixEnd_2491206 := by exact prefixLift 2491206
  have htrace : WordTrace (prefixWord ++ tailWord_2491206) baseStart_2491206 baseEnd_2491206 := by
    simpa [prefixWord, tailWord_2491206, baseEnd_2491206] using wordTrace_append hprefix tailTrace_2491206
  have hstable : (prefixWord ++ tailWord_2491206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491206).length < 2 ^ (prefixWord ++ tailWord_2491206).sum := by decide
  have hdescent : baseEnd_2491206 < baseStart_2491206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491228 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 6]
def baseStart_2491228 : Nat := 118140960795 + 2491228 * 2 ^ 59
def prefixEnd_2491228 : Nat := 4983230072969 + 3 ^ 40 * 2491228 * 2
def baseEnd_2491228 : Nat := 142133042659898254743673

theorem tailTrace_2491228 : CollatzResearch.WordTrace tailWord_2491228 prefixEnd_2491228 142133042659898254743673 := by
  unfold tailWord_2491228
  simp only [CollatzResearch.WordTrace]
  refine ⟨45431274909356949357141169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60575033212475932476188225 45431274909356949357141169)
  ·
    refine ⟨34073456182017712017855877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45431274909356949357141169 34073456182017712017855877)
    ·
      refine ⟨6388773034128321003347977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34073456182017712017855877 6388773034128321003347977)
      ·
        refine ⟨4791579775596240752510983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6388773034128321003347977 4791579775596240752510983)
        ·
          refine ⟨7187369663394361128766475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791579775596240752510983 7187369663394361128766475)
          ·
            refine ⟨10781054495091541693149713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187369663394361128766475 10781054495091541693149713)
            ·
              refine ⟨8085790871318656269862285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10781054495091541693149713 8085790871318656269862285)
              ·
                refine ⟨3032171576744496101198357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8085790871318656269862285 3032171576744496101198357)
                ·
                  refine ⟨142133042659898254743673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3032171576744496101198357 142133042659898254743673)
                  ·
                    rfl

theorem cell23_2491228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_2491228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491228 prefixEnd_2491228 := by exact prefixLift 2491228
  have htrace : WordTrace (prefixWord ++ tailWord_2491228) baseStart_2491228 baseEnd_2491228 := by
    simpa [prefixWord, tailWord_2491228, baseEnd_2491228] using wordTrace_append hprefix tailTrace_2491228
  have hstable : (prefixWord ++ tailWord_2491228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491228).length < 2 ^ (prefixWord ++ tailWord_2491228).sum := by decide
  have hdescent : baseEnd_2491228 < baseStart_2491228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491262 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2491262 : Nat := 118140960795 + 2491262 * 2 ^ 59
def prefixEnd_2491262 : Nat := 4983230072969 + 3 ^ 40 * 2491262 * 2
def baseEnd_2491262 : Nat := 142134982475704128851989

theorem tailTrace_2491262 : CollatzResearch.WordTrace tailWord_2491262 prefixEnd_2491262 142134982475704128851989 := by
  unfold tailWord_2491262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357973737573840315127505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60575859933727148347346693 11357973737573840315127505)
  ·
    refine ⟨8518480303180380236345629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11357973737573840315127505 8518480303180380236345629)
    ·
      refine ⟨3194430113692642588629611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8518480303180380236345629 3194430113692642588629611)
      ·
        refine ⟨4791645170538963882944417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194430113692642588629611 4791645170538963882944417)
        ·
          refine ⟨3593733877904222912208313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4791645170538963882944417 3593733877904222912208313)
          ·
            refine ⟨2695300408428167184156235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3593733877904222912208313 2695300408428167184156235)
            ·
              refine ⟨4042950612642250776234353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695300408428167184156235 4042950612642250776234353)
              ·
                refine ⟨3032212959481688082175765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4042950612642250776234353 3032212959481688082175765)
                ·
                  refine ⟨142134982475704128851989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3032212959481688082175765 142134982475704128851989)
                  ·
                    rfl

theorem cell23_2491262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2491262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491262 prefixEnd_2491262 := by exact prefixLift 2491262
  have htrace : WordTrace (prefixWord ++ tailWord_2491262) baseStart_2491262 baseEnd_2491262 := by
    simpa [prefixWord, tailWord_2491262, baseEnd_2491262] using wordTrace_append hprefix tailTrace_2491262
  have hstable : (prefixWord ++ tailWord_2491262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491262).length < 2 ^ (prefixWord ++ tailWord_2491262).sum := by decide
  have hdescent : baseEnd_2491262 < baseStart_2491262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491272 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2491272 : Nat := 118140960795 + 2491272 * 2 ^ 59
def prefixEnd_2491272 : Nat := 4983230072969 + 3 ^ 40 * 2491272 * 2
def baseEnd_2491272 : Nat := 1279219977087882120542855

theorem tailTrace_2491272 : CollatzResearch.WordTrace tailWord_2491272 prefixEnd_2491272 1279219977087882120542855 := by
  unfold tailWord_2491272
  simp only [CollatzResearch.WordTrace]
  refine ⟨45432077315277247114442035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60576103087036329485922713 45432077315277247114442035)
  ·
    refine ⟨68148115972915870671663053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45432077315277247114442035 68148115972915870671663053)
    ·
      refine ⟨25555543489843451501873645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68148115972915870671663053 25555543489843451501873645)
      ·
        refine ⟨9583328808691294313202617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25555543489843451501873645 9583328808691294313202617)
        ·
          refine ⟨7187496606518470734901963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9583328808691294313202617 7187496606518470734901963)
          ·
            refine ⟨10781244909777706102352945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187496606518470734901963 10781244909777706102352945)
            ·
              refine ⟨8085933682333279576764709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10781244909777706102352945 8085933682333279576764709)
              ·
                refine ⟨1516112565437489920643383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8085933682333279576764709 1516112565437489920643383)
                ·
                  refine ⟨2274168848156234880965075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516112565437489920643383 2274168848156234880965075)
                  ·
                    refine ⟨3411253272234352321447613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2274168848156234880965075 3411253272234352321447613)
                    ·
                      refine ⟨1279219977087882120542855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411253272234352321447613 1279219977087882120542855)
                      ·
                        rfl

theorem cell23_2491272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2491272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491272 prefixEnd_2491272 := by exact prefixLift 2491272
  have htrace : WordTrace (prefixWord ++ tailWord_2491272) baseStart_2491272 baseEnd_2491272 := by
    simpa [prefixWord, tailWord_2491272, baseEnd_2491272] using wordTrace_append hprefix tailTrace_2491272
  have hstable : (prefixWord ++ tailWord_2491272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491272).length < 2 ^ (prefixWord ++ tailWord_2491272).sum := by decide
  have hdescent : baseEnd_2491272 < baseStart_2491272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491295 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2491295 : Nat := 118140960795 + 2491295 * 2 ^ 59
def prefixEnd_2491295 : Nat := 4983230072969 + 3 ^ 40 * 2491295 * 2
def baseEnd_2491295 : Nat := 1279231787142935530555249

theorem tailTrace_2491295 : CollatzResearch.WordTrace tailWord_2491295 prefixEnd_2491295 1279231787142935530555249 := by
  unfold tailWord_2491295
  simp only [CollatzResearch.WordTrace]
  refine ⟨90864993509471169156971339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60576662339647446104647559 90864993509471169156971339)
  ·
    refine ⟨136297490264206753735457009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90864993509471169156971339 136297490264206753735457009)
    ·
      refine ⟨102223117698155065301592757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136297490264206753735457009 102223117698155065301592757)
      ·
        refine ⟨9583417284202037372024321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102223117698155065301592757 9583417284202037372024321)
        ·
          refine ⟨7187562963151528029018241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9583417284202037372024321 7187562963151528029018241)
          ·
            refine ⟨5390672222363646021763681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7187562963151528029018241 5390672222363646021763681)
            ·
              refine ⟨4043004166772734516322761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5390672222363646021763681 4043004166772734516322761)
              ·
                refine ⟨3032253125079550887242071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043004166772734516322761 3032253125079550887242071)
                ·
                  refine ⟨4548379687619326330863107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032253125079550887242071 4548379687619326330863107)
                  ·
                    refine ⟨6822569531428989496294661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4548379687619326330863107 6822569531428989496294661)
                    ·
                      refine ⟨1279231787142935530555249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6822569531428989496294661 1279231787142935530555249)
                      ·
                        rfl

theorem cell23_2491295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2491295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491295 prefixEnd_2491295 := by exact prefixLift 2491295
  have htrace : WordTrace (prefixWord ++ tailWord_2491295) baseStart_2491295 baseEnd_2491295 := by
    simpa [prefixWord, tailWord_2491295, baseEnd_2491295] using wordTrace_append hprefix tailTrace_2491295
  have hstable : (prefixWord ++ tailWord_2491295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491295).length < 2 ^ (prefixWord ++ tailWord_2491295).sum := by decide
  have hdescent : baseEnd_2491295 < baseStart_2491295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491338 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_2491338 : Nat := 118140960795 + 2491338 * 2 ^ 59
def prefixEnd_2491338 : Nat := 4983230072969 + 3 ^ 40 * 2491338 * 2
def baseEnd_2491338 : Nat := 1279253866811078862317551

theorem tailTrace_2491338 : CollatzResearch.WordTrace tailWord_2491338 prefixEnd_2491338 1279253866811078862317551 := by
  unfold tailWord_2491338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716640462078846875196667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60577707898876925000524445 22716640462078846875196667)
  ·
    refine ⟨34074960693118270312795001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22716640462078846875196667 34074960693118270312795001)
    ·
      refine ⟨25556220519838702734596251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34074960693118270312795001 25556220519838702734596251)
      ·
        refine ⟨38334330779758054101894377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25556220519838702734596251 38334330779758054101894377)
        ·
          refine ⟨28750748084818540576420783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38334330779758054101894377 28750748084818540576420783)
          ·
            refine ⟨43126122127227810864631175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28750748084818540576420783 43126122127227810864631175)
            ·
              refine ⟨64689183190841716296946763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43126122127227810864631175 64689183190841716296946763)
              ·
                refine ⟨97033774786262574445420145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64689183190841716296946763 97033774786262574445420145)
                ·
                  refine ⟨72775331089696930834065109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97033774786262574445420145 72775331089696930834065109)
                  ·
                    refine ⟨1705671822414771816423401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 72775331089696930834065109 1705671822414771816423401)
                    ·
                      refine ⟨1279253866811078862317551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705671822414771816423401 1279253866811078862317551)
                      ·
                        rfl

theorem cell23_2491338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_2491338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491338 prefixEnd_2491338 := by exact prefixLift 2491338
  have htrace : WordTrace (prefixWord ++ tailWord_2491338) baseStart_2491338 baseEnd_2491338 := by
    simpa [prefixWord, tailWord_2491338, baseEnd_2491338] using wordTrace_append hprefix tailTrace_2491338
  have hstable : (prefixWord ++ tailWord_2491338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491338).length < 2 ^ (prefixWord ++ tailWord_2491338).sum := by decide
  have hdescent : baseEnd_2491338 < baseStart_2491338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491345 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_2491345 : Nat := 118140960795 + 2491345 * 2 ^ 59
def prefixEnd_2491345 : Nat := 4983230072969 + 3 ^ 40 * 2491345 * 2
def baseEnd_2491345 : Nat := 1279257461175660334930019

theorem tailTrace_2491345 : CollatzResearch.WordTrace tailWord_2491345 prefixEnd_2491345 1279257461175660334930019 := by
  unfold tailWord_2491345
  simp only [CollatzResearch.WordTrace]
  refine ⟨90866817159290027696291489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60577878106193351797527659 90866817159290027696291489)
  ·
    refine ⟨68150112869467520772218617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90866817159290027696291489 68150112869467520772218617)
    ·
      refine ⟨51112584652100640579163963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68150112869467520772218617 51112584652100640579163963)
      ·
        refine ⟨76668876978150960868745945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51112584652100640579163963 76668876978150960868745945)
        ·
          refine ⟨57501657733613220651559459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76668876978150960868745945 57501657733613220651559459)
          ·
            refine ⟨86252486600419830977339189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57501657733613220651559459 86252486600419830977339189)
            ·
              refine ⟨8086170618789359154125549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86252486600419830977339189 8086170618789359154125549)
              ·
                refine ⟨3032313982046009682797081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8086170618789359154125549 3032313982046009682797081)
                ·
                  refine ⟨2274235486534507262097811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032313982046009682797081 2274235486534507262097811)
                  ·
                    refine ⟨3411353229801760893146717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2274235486534507262097811 3411353229801760893146717)
                    ·
                      refine ⟨1279257461175660334930019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411353229801760893146717 1279257461175660334930019)
                      ·
                        rfl

theorem cell23_2491345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_2491345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491345 prefixEnd_2491345 := by exact prefixLift 2491345
  have htrace : WordTrace (prefixWord ++ tailWord_2491345) baseStart_2491345 baseEnd_2491345 := by
    simpa [prefixWord, tailWord_2491345, baseEnd_2491345] using wordTrace_append hprefix tailTrace_2491345
  have hstable : (prefixWord ++ tailWord_2491345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491345).length < 2 ^ (prefixWord ++ tailWord_2491345).sum := by decide
  have hdescent : baseEnd_2491345 < baseStart_2491345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491349 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2491349 : Nat := 118140960795 + 2491349 * 2 ^ 59
def prefixEnd_2491349 : Nat := 4983230072969 + 3 ^ 40 * 2491349 * 2
def baseEnd_2491349 : Nat := 1279259515098278319280001

theorem tailTrace_2491349 : CollatzResearch.WordTrace tailWord_2491349 prefixEnd_2491349 1279259515098278319280001 := by
  unfold tailWord_2491349
  simp only [CollatzResearch.WordTrace]
  refine ⟨90866963051275536379437101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60577975367517024252958067 90866963051275536379437101)
  ·
    refine ⟨34075111144228326142288913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90866963051275536379437101 34075111144228326142288913)
    ·
      refine ⟨25556333358171244606716685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34075111144228326142288913 25556333358171244606716685)
      ·
        refine ⟨9583625009314216727518757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25556333358171244606716685 9583625009314216727518757)
        ·
          refine ⟨1796929689246415636409767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9583625009314216727518757 1796929689246415636409767)
          ·
            refine ⟨2695394533869623454614651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796929689246415636409767 2695394533869623454614651)
            ·
              refine ⟨4043091800804435181921977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695394533869623454614651 4043091800804435181921977)
              ·
                refine ⟨3032318850603326386441483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043091800804435181921977 3032318850603326386441483)
                ·
                  refine ⟨4548478275904989579662225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032318850603326386441483 4548478275904989579662225)
                  ·
                    refine ⟨3411358706928742184746669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4548478275904989579662225 3411358706928742184746669)
                    ·
                      refine ⟨1279259515098278319280001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411358706928742184746669 1279259515098278319280001)
                      ·
                        rfl

theorem cell23_2491349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2491349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491349 prefixEnd_2491349 := by exact prefixLift 2491349
  have htrace : WordTrace (prefixWord ++ tailWord_2491349) baseStart_2491349 baseEnd_2491349 := by
    simpa [prefixWord, tailWord_2491349, baseEnd_2491349] using wordTrace_append hprefix tailTrace_2491349
  have hstable : (prefixWord ++ tailWord_2491349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491349).length < 2 ^ (prefixWord ++ tailWord_2491349).sum := by decide
  have hdescent : baseEnd_2491349 < baseStart_2491349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491351 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2491351 : Nat := 118140960795 + 2491351 * 2 ^ 59
def prefixEnd_2491351 : Nat := 4983230072969 + 3 ^ 40 * 2491351 * 2
def baseEnd_2491351 : Nat := 1279260542059587311454991

theorem tailTrace_2491351 : CollatzResearch.WordTrace tailWord_2491351 prefixEnd_2491351 1279260542059587311454991 := by
  unfold tailWord_2491351
  simp only [CollatzResearch.WordTrace]
  refine ⟨90867035997268290721009907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60578023998178860480673271 90867035997268290721009907)
  ·
    refine ⟨136300553995902436081514861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90867035997268290721009907 136300553995902436081514861)
    ·
      refine ⟨51112707748463413530568073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136300553995902436081514861 51112707748463413530568073)
      ·
        refine ⟨38334530811347560147926055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51112707748463413530568073 38334530811347560147926055)
        ·
          refine ⟨57501796217021340221889083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38334530811347560147926055 57501796217021340221889083)
          ·
            refine ⟨86252694325532010332833625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57501796217021340221889083 86252694325532010332833625)
            ·
              refine ⟨64689520744149007749625219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86252694325532010332833625 64689520744149007749625219)
              ·
                refine ⟨97034281116223511624437829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64689520744149007749625219 97034281116223511624437829)
                ·
                  refine ⟨18193927709291908429582093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97034281116223511624437829 18193927709291908429582093)
                  ·
                    refine ⟨6822722890984465661093285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18193927709291908429582093 6822722890984465661093285)
                    ·
                      refine ⟨1279260542059587311454991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6822722890984465661093285 1279260542059587311454991)
                      ·
                        rfl

theorem cell23_2491351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2491351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491351 prefixEnd_2491351 := by exact prefixLift 2491351
  have htrace : WordTrace (prefixWord ++ tailWord_2491351) baseStart_2491351 baseEnd_2491351 := by
    simpa [prefixWord, tailWord_2491351, baseEnd_2491351] using wordTrace_append hprefix tailTrace_2491351
  have hstable : (prefixWord ++ tailWord_2491351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491351).length < 2 ^ (prefixWord ++ tailWord_2491351).sum := by decide
  have hdescent : baseEnd_2491351 < baseStart_2491351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491361 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2491361 : Nat := 118140960795 + 2491361 * 2 ^ 59
def prefixEnd_2491361 : Nat := 4983230072969 + 3 ^ 40 * 2491361 * 2
def baseEnd_2491361 : Nat := 426421892288710757443315

theorem tailTrace_2491361 : CollatzResearch.WordTrace tailWord_2491361 prefixEnd_2491361 426421892288710757443315 := by
  unfold tailWord_2491361
  simp only [CollatzResearch.WordTrace]
  refine ⟨90867400727232062428873937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60578267151488041619249291 90867400727232062428873937)
  ·
    refine ⟨68150550545424046821655453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90867400727232062428873937 68150550545424046821655453)
    ·
      refine ⟨25556456454534017558120795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68150550545424046821655453 25556456454534017558120795)
      ·
        refine ⟨38334684681801026337181193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25556456454534017558120795 38334684681801026337181193)
        ·
          refine ⟨28751013511350769752885895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38334684681801026337181193 28751013511350769752885895)
          ·
            refine ⟨43126520267026154629328843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28751013511350769752885895 43126520267026154629328843)
            ·
              refine ⟨64689780400539231943993265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43126520267026154629328843 64689780400539231943993265)
              ·
                refine ⟨48517335300404423957994949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64689780400539231943993265 48517335300404423957994949)
                ·
                  refine ⟨9097000368825829492124053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48517335300404423957994949 9097000368825829492124053)
                  ·
                    refine ⟨426421892288710757443315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9097000368825829492124053 426421892288710757443315)
                    ·
                      rfl

theorem cell23_2491361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2491361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491361 prefixEnd_2491361 := by exact prefixLift 2491361
  have htrace : WordTrace (prefixWord ++ tailWord_2491361) baseStart_2491361 baseEnd_2491361 := by
    simpa [prefixWord, tailWord_2491361, baseEnd_2491361] using wordTrace_append hprefix tailTrace_2491361
  have hstable : (prefixWord ++ tailWord_2491361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491361).length < 2 ^ (prefixWord ++ tailWord_2491361).sum := by decide
  have hdescent : baseEnd_2491361 < baseStart_2491361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491362 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2491362 : Nat := 118140960795 + 2491362 * 2 ^ 59
def prefixEnd_2491362 : Nat := 4983230072969 + 3 ^ 40 * 2491362 * 2
def baseEnd_2491362 : Nat := 1279266190346786768417441

theorem tailTrace_2491362 : CollatzResearch.WordTrace tailWord_2491362 prefixEnd_2491362 1279266190346786768417441 := by
  unfold tailWord_2491362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716859300057109899915085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60578291466818959733106893 22716859300057109899915085)
  ·
    refine ⟨8518822237521416212468157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22716859300057109899915085 8518822237521416212468157)
    ·
      refine ⟨3194558339070531079675559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8518822237521416212468157 3194558339070531079675559)
      ·
        refine ⟨4791837508605796619513339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194558339070531079675559 4791837508605796619513339)
        ·
          refine ⟨7187756262908694929270009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4791837508605796619513339 7187756262908694929270009)
          ·
            refine ⟨5390817197181521196952507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7187756262908694929270009 5390817197181521196952507)
            ·
              refine ⟨8086225795772281795428761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5390817197181521196952507 8086225795772281795428761)
              ·
                refine ⟨6064669346829211346571571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8086225795772281795428761 6064669346829211346571571)
                ·
                  refine ⟨9097004020243817019857357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064669346829211346571571 9097004020243817019857357)
                  ·
                    refine ⟨3411376507591431382446509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9097004020243817019857357 3411376507591431382446509)
                    ·
                      refine ⟨1279266190346786768417441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411376507591431382446509 1279266190346786768417441)
                      ·
                        rfl

theorem cell23_2491362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2491362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491362 prefixEnd_2491362 := by exact prefixLift 2491362
  have htrace : WordTrace (prefixWord ++ tailWord_2491362) baseStart_2491362 baseEnd_2491362 := by
    simpa [prefixWord, tailWord_2491362, baseEnd_2491362] using wordTrace_append hprefix tailTrace_2491362
  have hstable : (prefixWord ++ tailWord_2491362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491362).length < 2 ^ (prefixWord ++ tailWord_2491362).sum := by decide
  have hdescent : baseEnd_2491362 < baseStart_2491362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491388 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_2491388 : Nat := 118140960795 + 2491388 * 2 ^ 59
def prefixEnd_2491388 : Nat := 4983230072969 + 3 ^ 40 * 2491388 * 2
def baseEnd_2491388 : Nat := 1279279540843803666692321

theorem tailTrace_2491388 : CollatzResearch.WordTrace tailWord_2491388 prefixEnd_2491388 1279279540843803666692321 := by
  unfold tailWord_2491388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45434192749067123020053409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60578923665422830693404545 45434192749067123020053409)
  ·
    refine ⟨34075644561800342265040057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45434192749067123020053409 34075644561800342265040057)
    ·
      refine ⟨25556733421350256698780043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34075644561800342265040057 25556733421350256698780043)
      ·
        refine ⟨38335100132025385048170065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25556733421350256698780043 38335100132025385048170065)
        ·
          refine ⟨28751325099019038786127549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38335100132025385048170065 28751325099019038786127549)
          ·
            refine ⟨10781746912132139544797831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28751325099019038786127549 10781746912132139544797831)
            ·
              refine ⟨16172620368198209317196747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781746912132139544797831 16172620368198209317196747)
              ·
                refine ⟨24258930552297313975795121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16172620368198209317196747 24258930552297313975795121)
                ·
                  refine ⟨18194197914222985481846341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24258930552297313975795121 18194197914222985481846341)
                  ·
                    refine ⟨3411412108916809777846189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18194197914222985481846341 3411412108916809777846189)
                    ·
                      refine ⟨1279279540843803666692321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411412108916809777846189 1279279540843803666692321)
                      ·
                        rfl

theorem cell23_2491388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_2491388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491388 prefixEnd_2491388 := by exact prefixLift 2491388
  have htrace : WordTrace (prefixWord ++ tailWord_2491388) baseStart_2491388 baseEnd_2491388 := by
    simpa [prefixWord, tailWord_2491388, baseEnd_2491388] using wordTrace_append hprefix tailTrace_2491388
  have hstable : (prefixWord ++ tailWord_2491388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491388).length < 2 ^ (prefixWord ++ tailWord_2491388).sum := by decide
  have hdescent : baseEnd_2491388 < baseStart_2491388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491402 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_2491402 : Nat := 118140960795 + 2491402 * 2 ^ 59
def prefixEnd_2491402 : Nat := 4983230072969 + 3 ^ 40 * 2491402 * 2
def baseEnd_2491402 : Nat := 1279286729572966611917257

theorem tailTrace_2491402 : CollatzResearch.WordTrace tailWord_2491402 prefixEnd_2491402 1279286729572966611917257 := by
  unfold tailWord_2491402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22717224030020881607779115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60579264080055684287410973 22717224030020881607779115)
  ·
    refine ⟨34075836045031322411668673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22717224030020881607779115 34075836045031322411668673)
    ·
      refine ⟨25556877033773491808751505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34075836045031322411668673 25556877033773491808751505)
      ·
        refine ⟨19167657775330118856563629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25556877033773491808751505 19167657775330118856563629)
        ·
          refine ⟨7187871665748794571211361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19167657775330118856563629 7187871665748794571211361)
          ·
            refine ⟨5390903749311595928408521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7187871665748794571211361 5390903749311595928408521)
            ·
              refine ⟨4043177811983696946306391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5390903749311595928408521 4043177811983696946306391)
              ·
                refine ⟨6064766717975545419459587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043177811983696946306391 6064766717975545419459587)
                ·
                  refine ⟨9097150076963318129189381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064766717975545419459587 9097150076963318129189381)
                  ·
                    refine ⟨1705715639430622149223009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9097150076963318129189381 1705715639430622149223009)
                    ·
                      refine ⟨1279286729572966611917257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705715639430622149223009 1279286729572966611917257)
                      ·
                        rfl

theorem cell23_2491402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_2491402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491402 prefixEnd_2491402 := by exact prefixLift 2491402
  have htrace : WordTrace (prefixWord ++ tailWord_2491402) baseStart_2491402 baseEnd_2491402 := by
    simpa [prefixWord, tailWord_2491402, baseEnd_2491402] using wordTrace_append hprefix tailTrace_2491402
  have hstable : (prefixWord ++ tailWord_2491402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491402).length < 2 ^ (prefixWord ++ tailWord_2491402).sum := by decide
  have hdescent : baseEnd_2491402 < baseStart_2491402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491418 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_2491418 : Nat := 118140960795 + 2491418 * 2 ^ 59
def prefixEnd_2491418 : Nat := 4983230072969 + 3 ^ 40 * 2491418 * 2
def baseEnd_2491418 : Nat := 1279294945263438549317183

theorem tailTrace_2491418 : CollatzResearch.WordTrace tailWord_2491418 prefixEnd_2491418 1279294945263438549317183 := by
  unfold tailWord_2491418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22717369922006390290924727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60579653125350374109132605 22717369922006390290924727)
  ·
    refine ⟨34076054883009585436387091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22717369922006390290924727 34076054883009585436387091)
    ·
      refine ⟨51114082324514378154580637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34076054883009585436387091 51114082324514378154580637)
      ·
        refine ⟨19167780871692891807967739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51114082324514378154580637 19167780871692891807967739)
        ·
          refine ⟨28751671307539337711951609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19167780871692891807967739 28751671307539337711951609)
          ·
            refine ⟨21563753480654503283963707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28751671307539337711951609 21563753480654503283963707)
            ·
              refine ⟨32345630220981754925945561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21563753480654503283963707 32345630220981754925945561)
              ·
                refine ⟨24259222665736316194459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32345630220981754925945561 24259222665736316194459171)
                ·
                  refine ⟨36388833998604474291688757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24259222665736316194459171 36388833998604474291688757)
                  ·
                    refine ⟨3411453187369169464845821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36388833998604474291688757 3411453187369169464845821)
                    ·
                      refine ⟨1279294945263438549317183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411453187369169464845821 1279294945263438549317183)
                      ·
                        rfl

theorem cell23_2491418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_2491418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491418 prefixEnd_2491418 := by exact prefixLift 2491418
  have htrace : WordTrace (prefixWord ++ tailWord_2491418) baseStart_2491418 baseEnd_2491418 := by
    simpa [prefixWord, tailWord_2491418, baseEnd_2491418] using wordTrace_append hprefix tailTrace_2491418
  have hstable : (prefixWord ++ tailWord_2491418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491418).length < 2 ^ (prefixWord ++ tailWord_2491418).sum := by decide
  have hdescent : baseEnd_2491418 < baseStart_2491418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491425 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 5]
def baseStart_2491425 : Nat := 118140960795 + 2491425 * 2 ^ 59
def prefixEnd_2491425 : Nat := 4983230072969 + 3 ^ 40 * 2491425 * 2
def baseEnd_2491425 : Nat := 142144282180891113547739

theorem tailTrace_2491425 : CollatzResearch.WordTrace tailWord_2491425 prefixEnd_2491425 142144282180891113547739 := by
  unfold tailWord_2491425
  simp only [CollatzResearch.WordTrace]
  refine ⟨90869734999000201359203729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60579823332666800906135819 90869734999000201359203729)
  ·
    refine ⟨68152301249250151019402797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90869734999000201359203729 68152301249250151019402797)
    ·
      refine ⟨25557112968468806632276049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68152301249250151019402797 25557112968468806632276049)
      ·
        refine ⟨19167834726351604974207037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25557112968468806632276049 19167834726351604974207037)
        ·
          refine ⟨7187938022381851865327639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19167834726351604974207037 7187938022381851865327639)
          ·
            refine ⟨10781907033572777797991459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187938022381851865327639 10781907033572777797991459)
            ·
              refine ⟨16172860550359166696987189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781907033572777797991459 16172860550359166696987189)
              ·
                refine ⟨1516205676596171877842549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16172860550359166696987189 1516205676596171877842549)
                ·
                  refine ⟨142144282180891113547739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516205676596171877842549 142144282180891113547739)
                  ·
                    rfl

theorem cell23_2491425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 5].length) (baseStart_2491425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491425 prefixEnd_2491425 := by exact prefixLift 2491425
  have htrace : WordTrace (prefixWord ++ tailWord_2491425) baseStart_2491425 baseEnd_2491425 := by
    simpa [prefixWord, tailWord_2491425, baseEnd_2491425] using wordTrace_append hprefix tailTrace_2491425
  have hstable : (prefixWord ++ tailWord_2491425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491425).length < 2 ^ (prefixWord ++ tailWord_2491425).sum := by decide
  have hdescent : baseEnd_2491425 < baseStart_2491425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491451 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 8]
def baseStart_2491451 : Nat := 118140960795 + 2491451 * 2 ^ 59
def prefixEnd_2491451 : Nat := 4983230072969 + 3 ^ 40 * 2491451 * 2
def baseEnd_2491451 : Nat := 426437296708345640068177

theorem tailTrace_2491451 : CollatzResearch.WordTrace tailWord_2491451 prefixEnd_2491451 426437296708345640068177 := by
  unfold tailWord_2491451
  simp only [CollatzResearch.WordTrace]
  refine ⟨90870683296906007799650207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60580455531270671866433471 90870683296906007799650207)
  ·
    refine ⟨136306024945359011699475311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90870683296906007799650207 136306024945359011699475311)
    ·
      refine ⟨204459037418038517549212967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136306024945359011699475311 204459037418038517549212967)
      ·
        refine ⟨306688556127057776323819451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204459037418038517549212967 306688556127057776323819451)
        ·
          refine ⟨460032834190586664485729177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306688556127057776323819451 460032834190586664485729177)
          ·
            refine ⟨345024625642939998364296883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460032834190586664485729177 345024625642939998364296883)
            ·
              refine ⟨517536938464409997546445325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345024625642939998364296883 517536938464409997546445325)
              ·
                refine ⟨194076351924153749079916997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517536938464409997546445325 194076351924153749079916997)
                ·
                  refine ⟨36389315985778827952484437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194076351924153749079916997 36389315985778827952484437)
                  ·
                    refine ⟨426437296708345640068177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36389315985778827952484437 426437296708345640068177)
                    ·
                      rfl

theorem cell23_2491451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_2491451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491451 prefixEnd_2491451 := by exact prefixLift 2491451
  have htrace : WordTrace (prefixWord ++ tailWord_2491451) baseStart_2491451 baseEnd_2491451 := by
    simpa [prefixWord, tailWord_2491451, baseEnd_2491451] using wordTrace_append hprefix tailTrace_2491451
  have hstable : (prefixWord ++ tailWord_2491451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491451).length < 2 ^ (prefixWord ++ tailWord_2491451).sum := by decide
  have hdescent : baseEnd_2491451 < baseStart_2491451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491495 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2491495 : Nat := 118140960795 + 2491495 * 2 ^ 59
def prefixEnd_2491495 : Nat := 4983230072969 + 3 ^ 40 * 2491495 * 2
def baseEnd_2491495 : Nat := 1279334483273834748054329

theorem tailTrace_2491495 : CollatzResearch.WordTrace tailWord_2491495 prefixEnd_2491495 1279334483273834748054329 := by
  unfold tailWord_2491495
  simp only [CollatzResearch.WordTrace]
  refine ⟨90872288108746603314251939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60581525405831068876167959 90872288108746603314251939)
  ·
    refine ⟨136308432163119904971377909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90872288108746603314251939 136308432163119904971377909)
    ·
      refine ⟨12778915515292491091066679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136308432163119904971377909 12778915515292491091066679)
      ·
        refine ⟨19168373272938736636600019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12778915515292491091066679 19168373272938736636600019)
        ·
          refine ⟨28752559909408104954900029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19168373272938736636600019 28752559909408104954900029)
          ·
            refine ⟨10782209966028039358087511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28752559909408104954900029 10782209966028039358087511)
            ·
              refine ⟨16173314949042059037131267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782209966028039358087511 16173314949042059037131267)
              ·
                refine ⟨24259972423563088555696901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173314949042059037131267 24259972423563088555696901)
                ·
                  refine ⟨4548744829418079104193169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24259972423563088555696901 4548744829418079104193169)
                  ·
                    refine ⟨3411558622063559328144877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4548744829418079104193169 3411558622063559328144877)
                    ·
                      refine ⟨1279334483273834748054329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411558622063559328144877 1279334483273834748054329)
                      ·
                        rfl

theorem cell23_2491495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2491495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491495 prefixEnd_2491495 := by exact prefixLift 2491495
  have htrace : WordTrace (prefixWord ++ tailWord_2491495) baseStart_2491495 baseEnd_2491495 := by
    simpa [prefixWord, tailWord_2491495, baseEnd_2491495] using wordTrace_append hprefix tailTrace_2491495
  have hstable : (prefixWord ++ tailWord_2491495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491495).length < 2 ^ (prefixWord ++ tailWord_2491495).sum := by decide
  have hdescent : baseEnd_2491495 < baseStart_2491495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491502 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2491502 : Nat := 118140960795 + 2491502 * 2 ^ 59
def prefixEnd_2491502 : Nat := 4983230072969 + 3 ^ 40 * 2491502 * 2
def baseEnd_2491502 : Nat := 426446025879472073555599

theorem tailTrace_2491502 : CollatzResearch.WordTrace tailWord_2491502 prefixEnd_2491502 426446025879472073555599 := by
  unfold tailWord_2491502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359067927465155438719595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60581695613147495673171173 11359067927465155438719595)
  ·
    refine ⟨17038601891197733158079393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11359067927465155438719595 17038601891197733158079393)
    ·
      refine ⟨12778951418398299868559545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17038601891197733158079393 12778951418398299868559545)
      ·
        refine ⟨9584213563798724901419659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12778951418398299868559545 9584213563798724901419659)
        ·
          refine ⟨14376320345698087352129489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9584213563798724901419659 14376320345698087352129489)
          ·
            refine ⟨10782240259273565514097117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14376320345698087352129489 10782240259273565514097117)
            ·
              refine ⟨4043340097227587067786419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10782240259273565514097117 4043340097227587067786419)
              ·
                refine ⟨6065010145841380601679629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043340097227587067786419 6065010145841380601679629)
                ·
                  refine ⟨2274378804690517725629861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6065010145841380601679629 2274378804690517725629861)
                  ·
                    refine ⟨426446025879472073555599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274378804690517725629861 426446025879472073555599)
                    ·
                      rfl

theorem cell23_2491502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2491502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491502 prefixEnd_2491502 := by exact prefixLift 2491502
  have htrace : WordTrace (prefixWord ++ tailWord_2491502) baseStart_2491502 baseEnd_2491502 := by
    simpa [prefixWord, tailWord_2491502, baseEnd_2491502] using wordTrace_append hprefix tailTrace_2491502
  have hstable : (prefixWord ++ tailWord_2491502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491502).length < 2 ^ (prefixWord ++ tailWord_2491502).sum := by decide
  have hdescent : baseEnd_2491502 < baseStart_2491502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491552 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2]
def baseStart_2491552 : Nat := 118140960795 + 2491552 * 2 ^ 59
def prefixEnd_2491552 : Nat := 4983230072969 + 3 ^ 40 * 2491552 * 2
def baseEnd_2491552 : Nat := 1279363751671141025041567

theorem tailTrace_2491552 : CollatzResearch.WordTrace tailWord_2491552 prefixEnd_2491552 1279363751671141025041567 := by
  unfold tailWord_2491552
  simp only [CollatzResearch.WordTrace]
  refine ⟨45437183534770051024538455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60582911379693401366051273 45437183534770051024538455)
  ·
    refine ⟨68155775302155076536807683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45437183534770051024538455 68155775302155076536807683)
    ·
      refine ⟨102233662953232614805211525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68155775302155076536807683 102233662953232614805211525)
      ·
        refine ⟨19168811803731115275977161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102233662953232614805211525 19168811803731115275977161)
        ·
          refine ⟨14376608852798336456982871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19168811803731115275977161 14376608852798336456982871)
          ·
            refine ⟨21564913279197504685474307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14376608852798336456982871 21564913279197504685474307)
            ·
              refine ⟨32347369918796257028211461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21564913279197504685474307 32347369918796257028211461)
              ·
                refine ⟨6065131859774298192789649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32347369918796257028211461 6065131859774298192789649)
                ·
                  refine ⟨4548848894830723644592237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6065131859774298192789649 4548848894830723644592237)
                  ·
                    refine ⟨1705818335561521366722089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4548848894830723644592237 1705818335561521366722089)
                    ·
                      refine ⟨1279363751671141025041567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705818335561521366722089 1279363751671141025041567)
                      ·
                        rfl

theorem cell23_2491552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_2491552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491552 prefixEnd_2491552 := by exact prefixLift 2491552
  have htrace : WordTrace (prefixWord ++ tailWord_2491552) baseStart_2491552 baseEnd_2491552 := by
    simpa [prefixWord, tailWord_2491552, baseEnd_2491552] using wordTrace_append hprefix tailTrace_2491552
  have hstable : (prefixWord ++ tailWord_2491552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491552).length < 2 ^ (prefixWord ++ tailWord_2491552).sum := by decide
  have hdescent : baseEnd_2491552 < baseStart_2491552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491562 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2491562 : Nat := 118140960795 + 2491562 * 2 ^ 59
def prefixEnd_2491562 : Nat := 4983230072969 + 3 ^ 40 * 2491562 * 2
def baseEnd_2491562 : Nat := 426456295492561995305507

theorem tailTrace_2491562 : CollatzResearch.WordTrace tailWord_2491562 prefixEnd_2491562 426456295492561995305507 := by
  unfold tailWord_2491562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22718682949875968439235235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60583154533002582504627293 22718682949875968439235235)
  ·
    refine ⟨34078024424813952658852853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22718682949875968439235235 34078024424813952658852853)
    ·
      refine ⟨3194814789826308061767455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34078024424813952658852853 3194814789826308061767455)
      ·
        refine ⟨4792222184739462092651183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194814789826308061767455 4792222184739462092651183)
        ·
          refine ⟨7188333277109193138976775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792222184739462092651183 7188333277109193138976775)
          ·
            refine ⟨10782499915663789708465163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188333277109193138976775 10782499915663789708465163)
            ·
              refine ⟨16173749873495684562697745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782499915663789708465163 16173749873495684562697745)
              ·
                refine ⟨12130312405121763422023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16173749873495684562697745 12130312405121763422023309)
                ·
                  refine ⟨4548867151920661283258741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12130312405121763422023309 4548867151920661283258741)
                  ·
                    refine ⟨426456295492561995305507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4548867151920661283258741 426456295492561995305507)
                    ·
                      rfl

theorem cell23_2491562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2491562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491562 prefixEnd_2491562 := by exact prefixLift 2491562
  have htrace : WordTrace (prefixWord ++ tailWord_2491562) baseStart_2491562 baseEnd_2491562 := by
    simpa [prefixWord, tailWord_2491562, baseEnd_2491562] using wordTrace_append hprefix tailTrace_2491562
  have hstable : (prefixWord ++ tailWord_2491562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491562).length < 2 ^ (prefixWord ++ tailWord_2491562).sum := by decide
  have hdescent : baseEnd_2491562 < baseStart_2491562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491575 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 1, 6]
def baseStart_2491575 : Nat := 118140960795 + 2491575 * 2 ^ 59
def prefixEnd_2491575 : Nat := 4983230072969 + 3 ^ 40 * 2491575 * 2
def baseEnd_2491575 : Nat := 426458520575398145017987

theorem tailTrace_2491575 : CollatzResearch.WordTrace tailWord_2491575 prefixEnd_2491575 426458520575398145017987 := by
  unfold tailWord_2491575
  simp only [CollatzResearch.WordTrace]
  refine ⟨90875205948456776977164179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60583470632304517984776119 90875205948456776977164179)
  ·
    refine ⟨136312808922685165465746269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90875205948456776977164179 136312808922685165465746269)
    ·
      refine ⟨51117303346006937049654851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136312808922685165465746269 51117303346006937049654851)
      ·
        refine ⟨76675955019010405574482277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51117303346006937049654851 76675955019010405574482277)
        ·
          refine ⟨14376741566064451045215427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76675955019010405574482277 14376741566064451045215427)
          ·
            refine ⟨21565112349096676567823141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14376741566064451045215427 21565112349096676567823141)
            ·
              refine ⟨4043458565455626856466839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21565112349096676567823141 4043458565455626856466839)
              ·
                refine ⟨6065187848183440284700259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043458565455626856466839 6065187848183440284700259)
                ·
                  refine ⟨9097781772275160427050389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065187848183440284700259 9097781772275160427050389)
                  ·
                    refine ⟨426458520575398145017987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9097781772275160427050389 426458520575398145017987)
                    ·
                      rfl

theorem cell23_2491575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_2491575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491575 prefixEnd_2491575 := by exact prefixLift 2491575
  have htrace : WordTrace (prefixWord ++ tailWord_2491575) baseStart_2491575 baseEnd_2491575 := by
    simpa [prefixWord, tailWord_2491575, baseEnd_2491575] using wordTrace_append hprefix tailTrace_2491575
  have hstable : (prefixWord ++ tailWord_2491575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491575).length < 2 ^ (prefixWord ++ tailWord_2491575).sum := by decide
  have hdescent : baseEnd_2491575 < baseStart_2491575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491582 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2491582 : Nat := 118140960795 + 2491582 * 2 ^ 59
def prefixEnd_2491582 : Nat := 4983230072969 + 3 ^ 40 * 2491582 * 2
def baseEnd_2491582 : Nat := 1279379156090775907666429

theorem tailTrace_2491582 : CollatzResearch.WordTrace tailWord_2491582 prefixEnd_2491582 1279379156090775907666429 := by
  unfold tailWord_2491582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359432657428927146583625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60583640839620944781779333 11359432657428927146583625)
  ·
    refine ⟨8519574493071695359937719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11359432657428927146583625 8519574493071695359937719)
    ·
      refine ⟨12779361739607543039906579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8519574493071695359937719 12779361739607543039906579)
      ·
        refine ⟨19169042609411314559859869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12779361739607543039906579 19169042609411314559859869)
        ·
          refine ⟨7188390978529242959947451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19169042609411314559859869 7188390978529242959947451)
          ·
            refine ⟨10782586467793864439921177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188390978529242959947451 10782586467793864439921177)
            ·
              refine ⟨8086939850845398329940883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10782586467793864439921177 8086939850845398329940883)
              ·
                refine ⟨12130409776268097494911325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8086939850845398329940883 12130409776268097494911325)
                ·
                  refine ⟨4548903666100536560591747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12130409776268097494911325 4548903666100536560591747)
                  ·
                    refine ⟨6823355499150804840887621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4548903666100536560591747 6823355499150804840887621)
                    ·
                      refine ⟨1279379156090775907666429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6823355499150804840887621 1279379156090775907666429)
                      ·
                        rfl

theorem cell23_2491582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2491582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491582 prefixEnd_2491582 := by exact prefixLift 2491582
  have htrace : WordTrace (prefixWord ++ tailWord_2491582) baseStart_2491582 baseEnd_2491582 := by
    simpa [prefixWord, tailWord_2491582, baseEnd_2491582] using wordTrace_append hprefix tailTrace_2491582
  have hstable : (prefixWord ++ tailWord_2491582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491582).length < 2 ^ (prefixWord ++ tailWord_2491582).sum := by decide
  have hdescent : baseEnd_2491582 < baseStart_2491582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491605 : List Nat := [1, 3, 2, 4, 1, 2, 10]
def baseStart_2491605 : Nat := 118140960795 + 2491605 * 2 ^ 59
def prefixEnd_2491605 : Nat := 4983230072969 + 3 ^ 40 * 2491605 * 2
def baseEnd_2491605 : Nat := 15794950199331226144183

theorem tailTrace_2491605 : CollatzResearch.WordTrace tailWord_2491605 prefixEnd_2491605 15794950199331226144183 := by
  unfold tailWord_2491605
  simp only [CollatzResearch.WordTrace]
  refine ⟨90876300138348092100756269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60584200092232061400504179 90876300138348092100756269)
  ·
    refine ⟨34078612551880534537783601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90876300138348092100756269 34078612551880534537783601)
    ·
      refine ⟨25558959413910400903337701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34078612551880534537783601 25558959413910400903337701)
      ·
        refine ⟨4792304890108200169375819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25558959413910400903337701 4792304890108200169375819)
        ·
          refine ⟨7188457335162300254063729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792304890108200169375819 7188457335162300254063729)
          ·
            refine ⟨5391343001371725190547797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7188457335162300254063729 5391343001371725190547797)
            ·
              refine ⟨15794950199331226144183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5391343001371725190547797 15794950199331226144183)
              ·
                rfl

theorem cell23_2491605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 10].length) (baseStart_2491605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491605 prefixEnd_2491605 := by exact prefixLift 2491605
  have htrace : WordTrace (prefixWord ++ tailWord_2491605) baseStart_2491605 baseEnd_2491605 := by
    simpa [prefixWord, tailWord_2491605, baseEnd_2491605] using wordTrace_append hprefix tailTrace_2491605
  have hstable : (prefixWord ++ tailWord_2491605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491605).length < 2 ^ (prefixWord ++ tailWord_2491605).sum := by decide
  have hdescent : baseEnd_2491605 < baseStart_2491605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491615 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_2491615 : Nat := 118140960795 + 2491615 * 2 ^ 59
def prefixEnd_2491615 : Nat := 4983230072969 + 3 ^ 40 * 2491615 * 2
def baseEnd_2491615 : Nat := 1279396100952374278553777

theorem tailTrace_2491615 : CollatzResearch.WordTrace tailWord_2491615 prefixEnd_2491615 1279396100952374278553777 := by
  unfold tailWord_2491615
  simp only [CollatzResearch.WordTrace]
  refine ⟨90876664868311863808620299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60584443245541242539080199 90876664868311863808620299)
  ·
    refine ⟨136314997302467795712930449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90876664868311863808620299 136314997302467795712930449)
    ·
      refine ⟨102236247976850846784697837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136314997302467795712930449 102236247976850846784697837)
      ·
        refine ⟨38338592991319067544261689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102236247976850846784697837 38338592991319067544261689)
        ·
          refine ⟨28753944743489300658196267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38338592991319067544261689 28753944743489300658196267)
          ·
            refine ⟨43130917115233950987294401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28753944743489300658196267 43130917115233950987294401)
            ·
              refine ⟨32348187836425463240470801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43130917115233950987294401 32348187836425463240470801)
              ·
                refine ⟨24261140877319097430353101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32348187836425463240470801 24261140877319097430353101)
                ·
                  refine ⟨9097927828994661536382413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24261140877319097430353101 9097927828994661536382413)
                  ·
                    refine ⟨3411722935872998076143405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9097927828994661536382413 3411722935872998076143405)
                    ·
                      refine ⟨1279396100952374278553777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411722935872998076143405 1279396100952374278553777)
                      ·
                        rfl

theorem cell23_2491615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_2491615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491615 prefixEnd_2491615 := by exact prefixLift 2491615
  have htrace : WordTrace (prefixWord ++ tailWord_2491615) baseStart_2491615 baseEnd_2491615 := by
    simpa [prefixWord, tailWord_2491615, baseEnd_2491615] using wordTrace_append hprefix tailTrace_2491615
  have hstable : (prefixWord ++ tailWord_2491615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491615).length < 2 ^ (prefixWord ++ tailWord_2491615).sum := by decide
  have hdescent : baseEnd_2491615 < baseStart_2491615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491616 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 1, 2, 2]
def baseStart_2491616 : Nat := 118140960795 + 2491616 * 2 ^ 59
def prefixEnd_2491616 : Nat := 4983230072969 + 3 ^ 40 * 2491616 * 2
def baseEnd_2491616 : Nat := 1279396614433028774641273

theorem tailTrace_2491616 : CollatzResearch.WordTrace tailWord_2491616 prefixEnd_2491616 1279396614433028774641273 := by
  unfold tailWord_2491616
  simp only [CollatzResearch.WordTrace]
  refine ⟨45438350670654120489703351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60584467560872160652937801 45438350670654120489703351)
  ·
    refine ⟨68157526005981180734555027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45438350670654120489703351 68157526005981180734555027)
    ·
      refine ⟨102236289008971771101832541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68157526005981180734555027 102236289008971771101832541)
      ·
        refine ⟨38338608378364414163187203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102236289008971771101832541 38338608378364414163187203)
        ·
          refine ⟨57507912567546621244780805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38338608378364414163187203 57507912567546621244780805)
          ·
            refine ⟨10782733606414991483396401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57507912567546621244780805 10782733606414991483396401)
            ·
              refine ⟨8087050204811243612547301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10782733606414991483396401 8087050204811243612547301)
              ·
                refine ⟨1516321913402108177352619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8087050204811243612547301 1516321913402108177352619)
                ·
                  refine ⟨2274482870103162266028929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516321913402108177352619 2274482870103162266028929)
                  ·
                    refine ⟨1705862152577371699521697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2274482870103162266028929 1705862152577371699521697)
                    ·
                      refine ⟨1279396614433028774641273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705862152577371699521697 1279396614433028774641273)
                      ·
                        rfl

theorem cell23_2491616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_2491616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491616 prefixEnd_2491616 := by exact prefixLift 2491616
  have htrace : WordTrace (prefixWord ++ tailWord_2491616) baseStart_2491616 baseEnd_2491616 := by
    simpa [prefixWord, tailWord_2491616, baseEnd_2491616] using wordTrace_append hprefix tailTrace_2491616
  have hstable : (prefixWord ++ tailWord_2491616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491616).length < 2 ^ (prefixWord ++ tailWord_2491616).sum := by decide
  have hdescent : baseEnd_2491616 < baseStart_2491616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491629 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2491629 : Nat := 118140960795 + 2491629 * 2 ^ 59
def prefixEnd_2491629 : Nat := 4983230072969 + 3 ^ 40 * 2491629 * 2
def baseEnd_2491629 : Nat := 1279403289681537223778713

theorem tailTrace_2491629 : CollatzResearch.WordTrace tailWord_2491629 prefixEnd_2491629 1279403289681537223778713 := by
  unfold tailWord_2491629
  simp only [CollatzResearch.WordTrace]
  refine ⟨90877175490261144199629941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60584783660174096133086627 90877175490261144199629941)
  ·
    refine ⟨8519735202211982268715307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90877175490261144199629941 8519735202211982268715307)
    ·
      refine ⟨12779602803317973403072961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8519735202211982268715307 12779602803317973403072961)
      ·
        refine ⟨9584702102488480052304721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12779602803317973403072961 9584702102488480052304721)
        ·
          refine ⟨7188526576866360039228541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9584702102488480052304721 7188526576866360039228541)
          ·
            refine ⟨2695697466324885014710703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7188526576866360039228541 2695697466324885014710703)
            ·
              refine ⟨4043546199487327522066055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695697466324885014710703 4043546199487327522066055)
              ·
                refine ⟨6065319299230991283099083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043546199487327522066055 6065319299230991283099083)
                ·
                  refine ⟨9097978948846486924648625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065319299230991283099083 9097978948846486924648625)
                  ·
                    refine ⟨6823484211634865193486469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9097978948846486924648625 6823484211634865193486469)
                    ·
                      refine ⟨1279403289681537223778713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6823484211634865193486469 1279403289681537223778713)
                      ·
                        rfl

theorem cell23_2491629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2491629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491629 prefixEnd_2491629 := by exact prefixLift 2491629
  have htrace : WordTrace (prefixWord ++ tailWord_2491629) baseStart_2491629 baseEnd_2491629 := by
    simpa [prefixWord, tailWord_2491629, baseEnd_2491629] using wordTrace_append hprefix tailTrace_2491629
  have hstable : (prefixWord ++ tailWord_2491629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491629).length < 2 ^ (prefixWord ++ tailWord_2491629).sum := by decide
  have hdescent : baseEnd_2491629 < baseStart_2491629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491659 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 1, 3, 2]
def baseStart_2491659 : Nat := 118140960795 + 2491659 * 2 ^ 59
def prefixEnd_2491659 : Nat := 4983230072969 + 3 ^ 40 * 2491659 * 2
def baseEnd_2491659 : Nat := 1279418694101172106403575

theorem tailTrace_2491659 : CollatzResearch.WordTrace tailWord_2491659 prefixEnd_2491659 1279418694101172106403575 := by
  unfold tailWord_2491659
  simp only [CollatzResearch.WordTrace]
  refine ⟨90878269680152459323222031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60585513120101639548814687 90878269680152459323222031)
  ·
    refine ⟨136317404520228688984833047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90878269680152459323222031 136317404520228688984833047)
    ·
      refine ⟨204476106780343033477249571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136317404520228688984833047 204476106780343033477249571)
      ·
        refine ⟨306714160170514550215874357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204476106780343033477249571 306714160170514550215874357)
        ·
          refine ⟨28754452515985739082738221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 306714160170514550215874357 28754452515985739082738221)
          ·
            refine ⟨10782919693494652156026833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28754452515985739082738221 10782919693494652156026833)
            ·
              refine ⟨8087189770120989117020125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10782919693494652156026833 8087189770120989117020125)
              ·
                refine ⟨3032696163795370918882547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8087189770120989117020125 3032696163795370918882547)
                ·
                  refine ⟨4549044245693056378323821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032696163795370918882547 4549044245693056378323821)
                  ·
                    refine ⟨1705891592134896141871433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4549044245693056378323821 1705891592134896141871433)
                    ·
                      refine ⟨1279418694101172106403575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705891592134896141871433 1279418694101172106403575)
                      ·
                        rfl

theorem cell23_2491659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 3, 2].length) (baseStart_2491659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491659 prefixEnd_2491659 := by exact prefixLift 2491659
  have htrace : WordTrace (prefixWord ++ tailWord_2491659) baseStart_2491659 baseEnd_2491659 := by
    simpa [prefixWord, tailWord_2491659, baseEnd_2491659] using wordTrace_append hprefix tailTrace_2491659
  have hstable : (prefixWord ++ tailWord_2491659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491659).length < 2 ^ (prefixWord ++ tailWord_2491659).sum := by decide
  have hdescent : baseEnd_2491659 < baseStart_2491659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491675 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3]
def baseStart_2491675 : Nat := 118140960795 + 2491675 * 2 ^ 59
def prefixEnd_2491675 : Nat := 4983230072969 + 3 ^ 40 * 2491675 * 2
def baseEnd_2491675 : Nat := 1279426909791644043803501

theorem tailTrace_2491675 : CollatzResearch.WordTrace tailWord_2491675 prefixEnd_2491675 1279426909791644043803501 := by
  unfold tailWord_2491675
  simp only [CollatzResearch.WordTrace]
  refine ⟨90878853248094494055804479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60585902165396329370536319 90878853248094494055804479)
  ·
    refine ⟨136318279872141741083706719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90878853248094494055804479 136318279872141741083706719)
    ·
      refine ⟨204477419808212611625560079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136318279872141741083706719 204477419808212611625560079)
      ·
        refine ⟨306716129712318917438340119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204477419808212611625560079 306716129712318917438340119)
        ·
          refine ⟨460074194568478376157510179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306716129712318917438340119 460074194568478376157510179)
          ·
            refine ⟨690111291852717564236265269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460074194568478376157510179 690111291852717564236265269)
            ·
              refine ⟨64697933611192271647149869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 690111291852717564236265269 64697933611192271647149869)
              ·
                refine ⟨24261725104197101867681201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64697933611192271647149869 24261725104197101867681201)
                ·
                  refine ⟨18196293828147826400760901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24261725104197101867681201 18196293828147826400760901)
                  ·
                    refine ⟨3411805092777717450142669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18196293828147826400760901 3411805092777717450142669)
                    ·
                      refine ⟨1279426909791644043803501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411805092777717450142669 1279426909791644043803501)
                      ·
                        rfl

theorem cell23_2491675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3].length) (baseStart_2491675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491675 prefixEnd_2491675 := by exact prefixLift 2491675
  have htrace : WordTrace (prefixWord ++ tailWord_2491675) baseStart_2491675 baseEnd_2491675 := by
    simpa [prefixWord, tailWord_2491675, baseEnd_2491675] using wordTrace_append hprefix tailTrace_2491675
  have hstable : (prefixWord ++ tailWord_2491675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491675).length < 2 ^ (prefixWord ++ tailWord_2491675).sum := by decide
  have hdescent : baseEnd_2491675 < baseStart_2491675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491693 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2491693 : Nat := 118140960795 + 2491693 * 2 ^ 59
def prefixEnd_2491693 : Nat := 4983230072969 + 3 ^ 40 * 2491693 * 2
def baseEnd_2491693 : Nat := 1279436152443424973378419

theorem tailTrace_2491693 : CollatzResearch.WordTrace tailWord_2491693 prefixEnd_2491693 1279436152443424973378419 := by
  unfold tailWord_2491693
  simp only [CollatzResearch.WordTrace]
  refine ⟨90879509762029283129959733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60586339841352855419973155 90879509762029283129959733)
  ·
    refine ⟨8519954040190245293433725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90879509762029283129959733 8519954040190245293433725)
    ·
      refine ⟨3194982765071341985037647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8519954040190245293433725 3194982765071341985037647)
      ·
        refine ⟨4792474147607012977556471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194982765071341985037647 4792474147607012977556471)
        ·
          refine ⟨7188711221410519466334707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792474147607012977556471 7188711221410519466334707)
          ·
            refine ⟨10783066832115779199502061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188711221410519466334707 10783066832115779199502061)
            ·
              refine ⟨4043650062043417199813273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10783066832115779199502061 4043650062043417199813273)
              ·
                refine ⟨3032737546532562899859955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043650062043417199813273 3032737546532562899859955)
                ·
                  refine ⟨4549106319798844349789933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032737546532562899859955 4549106319798844349789933)
                  ·
                    refine ⟨1705914869924566631171225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4549106319798844349789933 1705914869924566631171225)
                    ·
                      refine ⟨1279436152443424973378419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705914869924566631171225 1279436152443424973378419)
                      ·
                        rfl

theorem cell23_2491693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2491693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491693 prefixEnd_2491693 := by exact prefixLift 2491693
  have htrace : WordTrace (prefixWord ++ tailWord_2491693) baseStart_2491693 baseEnd_2491693 := by
    simpa [prefixWord, tailWord_2491693, baseEnd_2491693] using wordTrace_append hprefix tailTrace_2491693
  have hstable : (prefixWord ++ tailWord_2491693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491693).length < 2 ^ (prefixWord ++ tailWord_2491693).sum := by decide
  have hdescent : baseEnd_2491693 < baseStart_2491693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491712 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 5]
def baseStart_2491712 : Nat := 118140960795 + 2491712 * 2 ^ 59
def prefixEnd_2491712 : Nat := 4983230072969 + 3 ^ 40 * 2491712 * 2
def baseEnd_2491712 : Nat := 142160656508428933226759

theorem tailTrace_2491712 : CollatzResearch.WordTrace tailWord_2491712 prefixEnd_2491712 142160656508428933226759 := by
  unfold tailWord_2491712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45440101374480224687450695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60586801832640299583267593 45440101374480224687450695)
  ·
    refine ⟨68160152061720337031176043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45440101374480224687450695 68160152061720337031176043)
    ·
      refine ⟨102240228092580505546764065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68160152061720337031176043 102240228092580505546764065)
      ·
        refine ⟨76680171069435379160073049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102240228092580505546764065 76680171069435379160073049)
        ·
          refine ⟨57510128302076534370054787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76680171069435379160073049 57510128302076534370054787)
          ·
            refine ⟨86265192453114801555082181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57510128302076534370054787 86265192453114801555082181)
            ·
              refine ⟨16174723584959025291577909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86265192453114801555082181 16174723584959025291577909)
              ·
                refine ⟨1516380336089908621085429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16174723584959025291577909 1516380336089908621085429)
                ·
                  refine ⟨142160656508428933226759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516380336089908621085429 142160656508428933226759)
                  ·
                    rfl

theorem cell23_2491712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 5].length) (baseStart_2491712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491712 prefixEnd_2491712 := by exact prefixLift 2491712
  have htrace : WordTrace (prefixWord ++ tailWord_2491712) baseStart_2491712 baseEnd_2491712 := by
    simpa [prefixWord, tailWord_2491712, baseEnd_2491712] using wordTrace_append hprefix tailTrace_2491712
  have hstable : (prefixWord ++ tailWord_2491712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491712).length < 2 ^ (prefixWord ++ tailWord_2491712).sum := by decide
  have hdescent : baseEnd_2491712 < baseStart_2491712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491762 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2491762 : Nat := 118140960795 + 2491762 * 2 ^ 59
def prefixEnd_2491762 : Nat := 4983230072969 + 3 ^ 40 * 2491762 * 2
def baseEnd_2491762 : Nat := 1279471582608585203415601

theorem tailTrace_2491762 : CollatzResearch.WordTrace tailWord_2491762 prefixEnd_2491762 1279471582608585203415601 := by
  unfold tailWord_2491762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22720506599694826978555385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60588017599186205276147693 22720506599694826978555385)
  ·
    refine ⟨17040379949771120233916539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22720506599694826978555385 17040379949771120233916539)
    ·
      refine ⟨25560569924656680350874809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17040379949771120233916539 25560569924656680350874809)
      ·
        refine ⟨19170427443492510263156107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25560569924656680350874809 19170427443492510263156107)
        ·
          refine ⟨28755641165238765394734161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19170427443492510263156107 28755641165238765394734161)
          ·
            refine ⟨21566730873929074046050621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28755641165238765394734161 21566730873929074046050621)
            ·
              refine ⟨8087524077723402767268983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21566730873929074046050621 8087524077723402767268983)
              ·
                refine ⟨12131286116585104150903475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087524077723402767268983 12131286116585104150903475)
                ·
                  refine ⟨18196929174877656226355213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131286116585104150903475 18196929174877656226355213)
                  ·
                    refine ⟨6823848440579121084883205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18196929174877656226355213 6823848440579121084883205)
                    ·
                      refine ⟨1279471582608585203415601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6823848440579121084883205 1279471582608585203415601)
                      ·
                        rfl

theorem cell23_2491762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2491762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491762 prefixEnd_2491762 := by exact prefixLift 2491762
  have htrace : WordTrace (prefixWord ++ tailWord_2491762) baseStart_2491762 baseEnd_2491762 := by
    simpa [prefixWord, tailWord_2491762, baseEnd_2491762] using wordTrace_append hprefix tailTrace_2491762
  have hstable : (prefixWord ++ tailWord_2491762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491762).length < 2 ^ (prefixWord ++ tailWord_2491762).sum := by decide
  have hdescent : baseEnd_2491762 < baseStart_2491762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491772 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_2491772 : Nat := 118140960795 + 2491772 * 2 ^ 59
def prefixEnd_2491772 : Nat := 4983230072969 + 3 ^ 40 * 2491772 * 2
def baseEnd_2491772 : Nat := 426492239138376721430185

theorem tailTrace_2491772 : CollatzResearch.WordTrace tailWord_2491772 prefixEnd_2491772 426492239138376721430185 := by
  unfold tailWord_2491772
  simp only [CollatzResearch.WordTrace]
  refine ⟨45441195564371539811042785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60588260752495386414723713 45441195564371539811042785)
  ·
    refine ⟨34080896673278654858282089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45441195564371539811042785 34080896673278654858282089)
    ·
      refine ⟨25560672504958991143711567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34080896673278654858282089 25560672504958991143711567)
      ·
        refine ⟨38341008757438486715567351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25560672504958991143711567 38341008757438486715567351)
        ·
          refine ⟨57511513136157730073351027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38341008757438486715567351 57511513136157730073351027)
          ·
            refine ⟨86267269704236595110026541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57511513136157730073351027 86267269704236595110026541)
            ·
              refine ⟨32350226139088723166259953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86267269704236595110026541 32350226139088723166259953)
              ·
                refine ⟨24262669604316542374694965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32350226139088723166259953 24262669604316542374694965)
                ·
                  refine ⟨2274625275404675847627653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24262669604316542374694965 2274625275404675847627653)
                  ·
                    refine ⟨426492239138376721430185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274625275404675847627653 426492239138376721430185)
                    ·
                      rfl

theorem cell23_2491772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_2491772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491772 prefixEnd_2491772 := by exact prefixLift 2491772
  have htrace : WordTrace (prefixWord ++ tailWord_2491772) baseStart_2491772 baseEnd_2491772 := by
    simpa [prefixWord, tailWord_2491772, baseEnd_2491772] using wordTrace_append hprefix tailTrace_2491772
  have hstable : (prefixWord ++ tailWord_2491772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491772).length < 2 ^ (prefixWord ++ tailWord_2491772).sum := by decide
  have hdescent : baseEnd_2491772 < baseStart_2491772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491774 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2491774 : Nat := 118140960795 + 2491774 * 2 ^ 59
def prefixEnd_2491774 : Nat := 4983230072969 + 3 ^ 40 * 2491774 * 2
def baseEnd_2491774 : Nat := 1279477744376439156465547

theorem tailTrace_2491774 : CollatzResearch.WordTrace tailWord_2491774 prefixEnd_2491774 1279477744376439156465547 := by
  unfold tailWord_2491774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11360308009341979245457297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60588309383157222642438917 11360308009341979245457297)
  ·
    refine ⟨8520231007006484434092973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11360308009341979245457297 8520231007006484434092973)
    ·
      refine ⟨3195086627627431662784865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8520231007006484434092973 3195086627627431662784865)
      ·
        refine ⟨2396314970720573747088649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3195086627627431662784865 2396314970720573747088649)
        ·
          refine ⟨1797236228040430310316487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2396314970720573747088649 1797236228040430310316487)
          ·
            refine ⟨2695854342060645465474731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797236228040430310316487 2695854342060645465474731)
            ·
              refine ⟨4043781513090968198212097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695854342060645465474731 4043781513090968198212097)
              ·
                refine ⟨3032836134818226148659073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043781513090968198212097 3032836134818226148659073)
                ·
                  refine ⟨2274627101113669611494305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032836134818226148659073 2274627101113669611494305)
                  ·
                    refine ⟨1705970325835252208620729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2274627101113669611494305 1705970325835252208620729)
                    ·
                      refine ⟨1279477744376439156465547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705970325835252208620729 1279477744376439156465547)
                      ·
                        rfl

theorem cell23_2491774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2491774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491774 prefixEnd_2491774 := by exact prefixLift 2491774
  have htrace : WordTrace (prefixWord ++ tailWord_2491774) baseStart_2491774 baseEnd_2491774 := by
    simpa [prefixWord, tailWord_2491774, baseEnd_2491774] using wordTrace_append hprefix tailTrace_2491774
  have hstable : (prefixWord ++ tailWord_2491774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491774).length < 2 ^ (prefixWord ++ tailWord_2491774).sum := by decide
  have hdescent : baseEnd_2491774 < baseStart_2491774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491779 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 2, 4, 2]
def baseStart_2491779 : Nat := 118140960795 + 2491779 * 2 ^ 59
def prefixEnd_2491779 : Nat := 4983230072969 + 3 ^ 40 * 2491779 * 2
def baseEnd_2491779 : Nat := 1279480311779711636903023

theorem tailTrace_2491779 : CollatzResearch.WordTrace tailWord_2491779 prefixEnd_2491779 1279480311779711636903023 := by
  unfold tailWord_2491779
  simp only [CollatzResearch.WordTrace]
  refine ⟨90882646439717719817590391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60588430959811813211726927 90882646439717719817590391)
  ·
    refine ⟨136323969659576579726385587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90882646439717719817590391 136323969659576579726385587)
    ·
      refine ⟨204485954489364869589578381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136323969659576579726385587 204485954489364869589578381)
      ·
        refine ⟨76682232933511826096091893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204485954489364869589578381 76682232933511826096091893)
        ·
          refine ⟨7188959337516733696508615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76682232933511826096091893 7188959337516733696508615)
          ·
            refine ⟨10783439006275100544762923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188959337516733696508615 10783439006275100544762923)
            ·
              refine ⟨16175158509412650817144385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10783439006275100544762923 16175158509412650817144385)
              ·
                refine ⟨12131368882059488112858289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16175158509412650817144385 12131368882059488112858289)
                ·
                  refine ⟨9098526661544616084643717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12131368882059488112858289 9098526661544616084643717)
                  ·
                    refine ⟨1705973749039615515870697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9098526661544616084643717 1705973749039615515870697)
                    ·
                      refine ⟨1279480311779711636903023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705973749039615515870697 1279480311779711636903023)
                      ·
                        rfl

theorem cell23_2491779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_2491779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491779 prefixEnd_2491779 := by exact prefixLift 2491779
  have htrace : WordTrace (prefixWord ++ tailWord_2491779) baseStart_2491779 baseEnd_2491779 := by
    simpa [prefixWord, tailWord_2491779, baseEnd_2491779] using wordTrace_append hprefix tailTrace_2491779
  have hstable : (prefixWord ++ tailWord_2491779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491779).length < 2 ^ (prefixWord ++ tailWord_2491779).sum := by decide
  have hdescent : baseEnd_2491779 < baseStart_2491779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491796 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2491796 : Nat := 118140960795 + 2491796 * 2 ^ 59
def prefixEnd_2491796 : Nat := 4983230072969 + 3 ^ 40 * 2491796 * 2
def baseEnd_2491796 : Nat := 1279489040950838070390445

theorem tailTrace_2491796 : CollatzResearch.WordTrace tailWord_2491796 prefixEnd_2491796 1279489040950838070390445 := by
  unfold tailWord_2491796
  simp only [CollatzResearch.WordTrace]
  refine ⟨45441633240328065860479621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60588844320437421147306161 45441633240328065860479621)
  ·
    refine ⟨8520306232561512348839929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45441633240328065860479621 8520306232561512348839929)
    ·
      refine ⟨6390229674421134261629947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8520306232561512348839929 6390229674421134261629947)
      ·
        refine ⟨9585344511631701392444921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390229674421134261629947 9585344511631701392444921)
        ·
          refine ⟨7189008383723776044333691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9585344511631701392444921 7189008383723776044333691)
          ·
            refine ⟨10783512575585664066500537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189008383723776044333691 10783512575585664066500537)
            ·
              refine ⟨8087634431689248049875403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10783512575585664066500537 8087634431689248049875403)
              ·
                refine ⟨12131451647533872074813105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087634431689248049875403 12131451647533872074813105)
                ·
                  refine ⟨9098588735650404056109829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12131451647533872074813105 9098588735650404056109829)
                  ·
                    refine ⟨1705985387934450760520593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9098588735650404056109829 1705985387934450760520593)
                    ·
                      refine ⟨1279489040950838070390445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1705985387934450760520593 1279489040950838070390445)
                      ·
                        rfl

theorem cell23_2491796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2491796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491796 prefixEnd_2491796 := by exact prefixLift 2491796
  have htrace : WordTrace (prefixWord ++ tailWord_2491796) baseStart_2491796 baseEnd_2491796 := by
    simpa [prefixWord, tailWord_2491796, baseEnd_2491796] using wordTrace_append hprefix tailTrace_2491796
  have hstable : (prefixWord ++ tailWord_2491796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491796).length < 2 ^ (prefixWord ++ tailWord_2491796).sum := by decide
  have hdescent : baseEnd_2491796 < baseStart_2491796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491812 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_2491812 : Nat := 118140960795 + 2491812 * 2 ^ 59
def prefixEnd_2491812 : Nat := 4983230072969 + 3 ^ 40 * 2491812 * 2
def baseEnd_2491812 : Nat := 1279497256641310007790371

theorem tailTrace_2491812 : CollatzResearch.WordTrace tailWord_2491812 prefixEnd_2491812 1279497256641310007790371 := by
  unfold tailWord_2491812
  simp only [CollatzResearch.WordTrace]
  refine ⟨45441925024299083226770845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60589233365732110969027793 45441925024299083226770845)
  ·
    refine ⟨17040721884112156210039067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45441925024299083226770845 17040721884112156210039067)
    ·
      refine ⟨25561082826168234315058601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17040721884112156210039067 25561082826168234315058601)
      ·
        refine ⟨19170812119626175736293951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25561082826168234315058601 19170812119626175736293951)
        ·
          refine ⟨28756218179439263604440927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19170812119626175736293951 28756218179439263604440927)
          ·
            refine ⟨43134327269158895406661391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28756218179439263604440927 43134327269158895406661391)
            ·
              refine ⟨64701490903738343109992087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43134327269158895406661391 64701490903738343109992087)
              ·
                refine ⟨97052236355607514664988131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64701490903738343109992087 97052236355607514664988131)
                ·
                  refine ⟨145578354533411271997482197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97052236355607514664988131 145578354533411271997482197)
                  ·
                    refine ⟨3411992684376826687440989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145578354533411271997482197 3411992684376826687440989)
                    ·
                      refine ⟨1279497256641310007790371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3411992684376826687440989 1279497256641310007790371)
                      ·
                        rfl

theorem cell23_2491812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_2491812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491812 prefixEnd_2491812 := by exact prefixLift 2491812
  have htrace : WordTrace (prefixWord ++ tailWord_2491812) baseStart_2491812 baseEnd_2491812 := by
    simpa [prefixWord, tailWord_2491812, baseEnd_2491812] using wordTrace_append hprefix tailTrace_2491812
  have hstable : (prefixWord ++ tailWord_2491812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491812).length < 2 ^ (prefixWord ++ tailWord_2491812).sum := by decide
  have hdescent : baseEnd_2491812 < baseStart_2491812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491866 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_2491866 : Nat := 118140960795 + 2491866 * 2 ^ 59
def prefixEnd_2491866 : Nat := 4983230072969 + 3 ^ 40 * 2491866 * 2
def baseEnd_2491866 : Nat := 426508328198884265505041

theorem tailTrace_2491866 : CollatzResearch.WordTrace tailWord_2491866 prefixEnd_2491866 426508328198884265505041 := by
  unfold tailWord_2491866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22721454897600633419001863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60590546393601689117338301 22721454897600633419001863)
  ·
    refine ⟨34082182346400950128502795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22721454897600633419001863 34082182346400950128502795)
    ·
      refine ⟨51123273519601425192754193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34082182346400950128502795 51123273519601425192754193)
      ·
        refine ⟨38342455139701068894565645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51123273519601425192754193 38342455139701068894565645)
        ·
          refine ⟨14378420677387900835462117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38342455139701068894565645 14378420677387900835462117)
          ·
            refine ⟨2695953877010231406649147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14378420677387900835462117 2695953877010231406649147)
            ·
              refine ⟨4043930815515347109973721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695953877010231406649147 4043930815515347109973721)
              ·
                refine ⟨3032948111636510332480291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043930815515347109973721 3032948111636510332480291)
                ·
                  refine ⟨4549422167454765498720437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032948111636510332480291 4549422167454765498720437)
                  ·
                    refine ⟨426508328198884265505041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4549422167454765498720437 426508328198884265505041)
                    ·
                      rfl

theorem cell23_2491866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_2491866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491866 prefixEnd_2491866 := by exact prefixLift 2491866
  have htrace : WordTrace (prefixWord ++ tailWord_2491866) baseStart_2491866 baseEnd_2491866 := by
    simpa [prefixWord, tailWord_2491866, baseEnd_2491866] using wordTrace_append hprefix tailTrace_2491866
  have hstable : (prefixWord ++ tailWord_2491866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491866).length < 2 ^ (prefixWord ++ tailWord_2491866).sum := by decide
  have hdescent : baseEnd_2491866 < baseStart_2491866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491879 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2491879 : Nat := 118140960795 + 2491879 * 2 ^ 59
def prefixEnd_2491879 : Nat := 4983230072969 + 3 ^ 40 * 2491879 * 2
def baseEnd_2491879 : Nat := 426510553281720415217521

theorem tailTrace_2491879 : CollatzResearch.WordTrace tailWord_2491879 prefixEnd_2491879 426510553281720415217521 := by
  unfold tailWord_2491879
  simp only [CollatzResearch.WordTrace]
  refine ⟨90886293739355436896230691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60590862492903624597487127 90886293739355436896230691)
  ·
    refine ⟨136329440609033155344346037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90886293739355436896230691 136329440609033155344346037)
    ·
      refine ⟨12780885057096858313532441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136329440609033155344346037 12780885057096858313532441)
      ·
        refine ⟨9585663792822643735149331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12780885057096858313532441 9585663792822643735149331)
        ·
          refine ⟨14378495689233965602723997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9585663792822643735149331 14378495689233965602723997)
          ·
            refine ⟨5391935883462737101021499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14378495689233965602723997 5391935883462737101021499)
            ·
              refine ⟨8087903825194105651532249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391935883462737101021499 8087903825194105651532249)
              ·
                refine ⟨6065927868895579238649187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8087903825194105651532249 6065927868895579238649187)
                ·
                  refine ⟨9098891803343368857973781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065927868895579238649187 9098891803343368857973781)
                  ·
                    refine ⟨426510553281720415217521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9098891803343368857973781 426510553281720415217521)
                    ·
                      rfl

theorem cell23_2491879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2491879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491879 prefixEnd_2491879 := by exact prefixLift 2491879
  have htrace : WordTrace (prefixWord ++ tailWord_2491879) baseStart_2491879 baseEnd_2491879 := by
    simpa [prefixWord, tailWord_2491879, baseEnd_2491879] using wordTrace_append hprefix tailTrace_2491879
  have hstable : (prefixWord ++ tailWord_2491879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491879).length < 2 ^ (prefixWord ++ tailWord_2491879).sum := by decide
  have hdescent : baseEnd_2491879 < baseStart_2491879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491889 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_2491889 : Nat := 118140960795 + 2491889 * 2 ^ 59
def prefixEnd_2491889 : Nat := 4983230072969 + 3 ^ 40 * 2491889 * 2
def baseEnd_2491889 : Nat := 1279536794651706206527517

theorem tailTrace_2491889 : CollatzResearch.WordTrace tailWord_2491889 prefixEnd_2491889 1279536794651706206527517 := by
  unfold tailWord_2491889
  simp only [CollatzResearch.WordTrace]
  refine ⟨90886658469319208604094721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60591105646212805736063147 90886658469319208604094721)
  ·
    refine ⟨68164993851989406453071041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90886658469319208604094721 68164993851989406453071041)
    ·
      refine ⟨51123745388992054839803281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68164993851989406453071041 51123745388992054839803281)
      ·
        refine ⟨38342809041744041129852461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51123745388992054839803281 38342809041744041129852461)
        ·
          refine ⟨14378553390654015423694673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38342809041744041129852461 14378553390654015423694673)
          ·
            refine ⟨10783915042990511567771005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14378553390654015423694673 10783915042990511567771005)
            ·
              refine ⟨4043968141121441837914127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10783915042990511567771005 4043968141121441837914127)
              ·
                refine ⟨6065952211682162756871191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043968141121441837914127 6065952211682162756871191)
                ·
                  refine ⟨9098928317523244135306787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065952211682162756871191 9098928317523244135306787)
                  ·
                    refine ⟨13648392476284866202960181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9098928317523244135306787 13648392476284866202960181)
                    ·
                      refine ⟨1279536794651706206527517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13648392476284866202960181 1279536794651706206527517)
                      ·
                        rfl

theorem cell23_2491889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_2491889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491889 prefixEnd_2491889 := by exact prefixLift 2491889
  have htrace : WordTrace (prefixWord ++ tailWord_2491889) baseStart_2491889 baseEnd_2491889 := by
    simpa [prefixWord, tailWord_2491889, baseEnd_2491889] using wordTrace_append hprefix tailTrace_2491889
  have hstable : (prefixWord ++ tailWord_2491889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491889).length < 2 ^ (prefixWord ++ tailWord_2491889).sum := by decide
  have hdescent : baseEnd_2491889 < baseStart_2491889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491896 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_2491896 : Nat := 118140960795 + 2491896 * 2 ^ 59
def prefixEnd_2491896 : Nat := 4983230072969 + 3 ^ 40 * 2491896 * 2
def baseEnd_2491896 : Nat := 426513463005429226379995

theorem tailTrace_2491896 : CollatzResearch.WordTrace tailWord_2491896 prefixEnd_2491896 426513463005429226379995 := by
  unfold tailWord_2491896
  simp only [CollatzResearch.WordTrace]
  refine ⟨45443456890146924399799771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60591275853529232533066361 45443456890146924399799771)
  ·
    refine ⟨68165185335220386599699657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45443456890146924399799771 68165185335220386599699657)
    ·
      refine ⟨51123889001415289949774743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68165185335220386599699657 51123889001415289949774743)
      ·
        refine ⟨76685833502122934924662115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51123889001415289949774743 76685833502122934924662115)
        ·
          refine ⟨115028750253184402386993173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76685833502122934924662115 115028750253184402386993173)
          ·
            refine ⟨5391972668118018861890305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115028750253184402386993173 5391972668118018861890305)
            ·
              refine ⟨4043979501088514146417729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5391972668118018861890305 4043979501088514146417729)
              ·
                refine ⟨3032984625816385609813297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4043979501088514146417729 3032984625816385609813297)
                ·
                  refine ⟨2274738469362289207359973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032984625816385609813297 2274738469362289207359973)
                  ·
                    refine ⟨426513463005429226379995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274738469362289207359973 426513463005429226379995)
                    ·
                      rfl

theorem cell23_2491896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_2491896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491896 prefixEnd_2491896 := by exact prefixLift 2491896
  have htrace : WordTrace (prefixWord ++ tailWord_2491896) baseStart_2491896 baseEnd_2491896 := by
    simpa [prefixWord, tailWord_2491896, baseEnd_2491896] using wordTrace_append hprefix tailTrace_2491896
  have hstable : (prefixWord ++ tailWord_2491896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491896).length < 2 ^ (prefixWord ++ tailWord_2491896).sum := by decide
  have hdescent : baseEnd_2491896 < baseStart_2491896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491912 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2491912 : Nat := 118140960795 + 2491912 * 2 ^ 59
def prefixEnd_2491912 : Nat := 4983230072969 + 3 ^ 40 * 2491912 * 2
def baseEnd_2491912 : Nat := 1279548604706759616539911

theorem tailTrace_2491912 : CollatzResearch.WordTrace tailWord_2491912 prefixEnd_2491912 1279548604706759616539911 := by
  unfold tailWord_2491912
  simp only [CollatzResearch.WordTrace]
  refine ⟨45443748674117941766090995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60591664898823922354787993 45443748674117941766090995)
  ·
    refine ⟨68165623011176912649136493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45443748674117941766090995 68165623011176912649136493)
    ·
      refine ⟨25562108629191342243426185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68165623011176912649136493 25562108629191342243426185)
      ·
        refine ⟨19171581471893506682569639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25562108629191342243426185 19171581471893506682569639)
        ·
          refine ⟨28757372207840260023854459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19171581471893506682569639 28757372207840260023854459)
          ·
            refine ⟨43136058311760390035781689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28757372207840260023854459 43136058311760390035781689)
            ·
              refine ⟨32352043733820292526836267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43136058311760390035781689 32352043733820292526836267)
              ·
                refine ⟨48528065600730438790254401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32352043733820292526836267 48528065600730438790254401)
                ·
                  refine ⟨36396049200547829092690801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48528065600730438790254401 36396049200547829092690801)
                  ·
                    refine ⟨27297036900410871819518101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36396049200547829092690801 27297036900410871819518101)
                    ·
                      refine ⟨1279548604706759616539911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27297036900410871819518101 1279548604706759616539911)
                      ·
                        rfl

theorem cell23_2491912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2491912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491912 prefixEnd_2491912 := by exact prefixLift 2491912
  have htrace : WordTrace (prefixWord ++ tailWord_2491912) baseStart_2491912 baseEnd_2491912 := by
    simpa [prefixWord, tailWord_2491912, baseEnd_2491912] using wordTrace_append hprefix tailTrace_2491912
  have hstable : (prefixWord ++ tailWord_2491912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491912).length < 2 ^ (prefixWord ++ tailWord_2491912).sum := by decide
  have hdescent : baseEnd_2491912 < baseStart_2491912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491916 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2491916 : Nat := 118140960795 + 2491916 * 2 ^ 59
def prefixEnd_2491916 : Nat := 4983230072969 + 3 ^ 40 * 2491916 * 2
def baseEnd_2491916 : Nat := 1279550658629377600889893

theorem tailTrace_2491916 : CollatzResearch.WordTrace tailWord_2491916 prefixEnd_2491916 1279550658629377600889893 := by
  unfold tailWord_2491916
  simp only [CollatzResearch.WordTrace]
  refine ⟨45443821620110696107663801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60591762160147594810218401 45443821620110696107663801)
  ·
    refine ⟨34082866215083022080747851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45443821620110696107663801 34082866215083022080747851)
    ·
      refine ⟨51124299322624533121121777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34082866215083022080747851 51124299322624533121121777)
      ·
        refine ⟨38343224491968399840841333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51124299322624533121121777 38343224491968399840841333)
        ·
          refine ⟨3594677296122037485078875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38343224491968399840841333 3594677296122037485078875)
          ·
            refine ⟨5392015944183056227618313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594677296122037485078875 5392015944183056227618313)
            ·
              refine ⟨4044011958137292170713735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392015944183056227618313 4044011958137292170713735)
              ·
                refine ⟨6066017937205938256070603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044011958137292170713735 6066017937205938256070603)
                ·
                  refine ⟨9099026905808907384105905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066017937205938256070603 9099026905808907384105905)
                  ·
                    refine ⟨6824270179356680538079429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9099026905808907384105905 6824270179356680538079429)
                    ·
                      refine ⟨1279550658629377600889893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6824270179356680538079429 1279550658629377600889893)
                      ·
                        rfl

theorem cell23_2491916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2491916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491916 prefixEnd_2491916 := by exact prefixLift 2491916
  have htrace : WordTrace (prefixWord ++ tailWord_2491916) baseStart_2491916 baseEnd_2491916 := by
    simpa [prefixWord, tailWord_2491916, baseEnd_2491916] using wordTrace_append hprefix tailTrace_2491916
  have hstable : (prefixWord ++ tailWord_2491916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491916).length < 2 ^ (prefixWord ++ tailWord_2491916).sum := by decide
  have hdescent : baseEnd_2491916 < baseStart_2491916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491934 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2491934 : Nat := 118140960795 + 2491934 * 2 ^ 59
def prefixEnd_2491934 : Nat := 4983230072969 + 3 ^ 40 * 2491934 * 2
def baseEnd_2491934 : Nat := 426519967093719510154937

theorem tailTrace_2491934 : CollatzResearch.WordTrace tailWord_2491934 prefixEnd_2491934 426519967093719510154937 := by
  unfold tailWord_2491934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361037469269522661185357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60592199836104120859655237 11361037469269522661185357)
  ·
    refine ⟨4260389050976070997944509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11361037469269522661185357 4260389050976070997944509)
    ·
      refine ⟨1597645894116026624229191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4260389050976070997944509 1597645894116026624229191)
      ·
        refine ⟨2396468841174039936343787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597645894116026624229191 2396468841174039936343787)
        ·
          refine ⟨3594703261761059904515681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396468841174039936343787 3594703261761059904515681)
          ·
            refine ⟨2696027446320794928386761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3594703261761059904515681 2696027446320794928386761)
            ·
              refine ⟨2022020584740596196290071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696027446320794928386761 2022020584740596196290071)
              ·
                refine ⟨3033030877110894294435107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022020584740596196290071 3033030877110894294435107)
                ·
                  refine ⟨4549546315666341441652661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033030877110894294435107 4549546315666341441652661)
                  ·
                    refine ⟨426519967093719510154937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4549546315666341441652661 426519967093719510154937)
                    ·
                      rfl

theorem cell23_2491934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2491934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491934 prefixEnd_2491934 := by exact prefixLift 2491934
  have htrace : WordTrace (prefixWord ++ tailWord_2491934) baseStart_2491934 baseEnd_2491934 := by
    simpa [prefixWord, tailWord_2491934, baseEnd_2491934] using wordTrace_append hprefix tailTrace_2491934
  have hstable : (prefixWord ++ tailWord_2491934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491934).length < 2 ^ (prefixWord ++ tailWord_2491934).sum := by decide
  have hdescent : baseEnd_2491934 < baseStart_2491934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491936 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2491936 : Nat := 118140960795 + 2491936 * 2 ^ 59
def prefixEnd_2491936 : Nat := 4983230072969 + 3 ^ 40 * 2491936 * 2
def baseEnd_2491936 : Nat := 1279560928242467522639801

theorem tailTrace_2491936 : CollatzResearch.WordTrace tailWord_2491936 prefixEnd_2491936 1279560928242467522639801 := by
  unfold tailWord_2491936
  simp only [CollatzResearch.WordTrace]
  refine ⟨45444186350074467815527831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60592248466765957087370441 45444186350074467815527831)
  ·
    refine ⟨68166279525111701723291747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45444186350074467815527831 68166279525111701723291747)
    ·
      refine ⟨102249419287667552584937621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68166279525111701723291747 102249419287667552584937621)
      ·
        refine ⟨4792941529109416527418951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102249419287667552584937621 4792941529109416527418951)
        ·
          refine ⟨7189412293664124791128427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792941529109416527418951 7189412293664124791128427)
          ·
            refine ⟨10784118440496187186692641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189412293664124791128427 10784118440496187186692641)
            ·
              refine ⟨8088088830372140390019481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10784118440496187186692641 8088088830372140390019481)
              ·
                refine ⟨6066066622779105292514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8088088830372140390019481 6066066622779105292514611)
                ·
                  refine ⟨9099099934168657938771917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066066622779105292514611 9099099934168657938771917)
                  ·
                    refine ⟨3412162475313246727039469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9099099934168657938771917 3412162475313246727039469)
                    ·
                      refine ⟨1279560928242467522639801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3412162475313246727039469 1279560928242467522639801)
                      ·
                        rfl

theorem cell23_2491936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2491936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491936 prefixEnd_2491936 := by exact prefixLift 2491936
  have htrace : WordTrace (prefixWord ++ tailWord_2491936) baseStart_2491936 baseEnd_2491936 := by
    simpa [prefixWord, tailWord_2491936, baseEnd_2491936] using wordTrace_append hprefix tailTrace_2491936
  have hstable : (prefixWord ++ tailWord_2491936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491936).length < 2 ^ (prefixWord ++ tailWord_2491936).sum := by decide
  have hdescent : baseEnd_2491936 < baseStart_2491936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491969 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2491969 : Nat := 118140960795 + 2491969 * 2 ^ 59
def prefixEnd_2491969 : Nat := 4983230072969 + 3 ^ 40 * 2491969 * 2
def baseEnd_2491969 : Nat := 426525957701355297842383

theorem tailTrace_2491969 : CollatzResearch.WordTrace tailWord_2491969 prefixEnd_2491969 426525957701355297842383 := by
  unfold tailWord_2491969
  simp only [CollatzResearch.WordTrace]
  refine ⟨90889576309029382267006961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60593050872686254844671307 90889576309029382267006961)
  ·
    refine ⟨68167182231772036700255221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90889576309029382267006961 68167182231772036700255221)
    ·
      refine ⟨6390673334228628440648927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68167182231772036700255221 6390673334228628440648927)
      ·
        refine ⟨9586010001342942660973391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390673334228628440648927 9586010001342942660973391)
        ·
          refine ⟨14379015002014413991460087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586010001342942660973391 14379015002014413991460087)
          ·
            refine ⟨21568522503021620987190131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14379015002014413991460087 21568522503021620987190131)
            ·
              refine ⟨32352783754532431480785197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21568522503021620987190131 32352783754532431480785197)
              ·
                refine ⟨12132293907949661805294449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32352783754532431480785197 12132293907949661805294449)
                ·
                  refine ⟨9099220430962246353970837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12132293907949661805294449 9099220430962246353970837)
                  ·
                    refine ⟨426525957701355297842383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9099220430962246353970837 426525957701355297842383)
                    ·
                      rfl

theorem cell23_2491969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2491969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491969 prefixEnd_2491969 := by exact prefixLift 2491969
  have htrace : WordTrace (prefixWord ++ tailWord_2491969) baseStart_2491969 baseEnd_2491969 := by
    simpa [prefixWord, tailWord_2491969, baseEnd_2491969] using wordTrace_append hprefix tailTrace_2491969
  have hstable : (prefixWord ++ tailWord_2491969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491969).length < 2 ^ (prefixWord ++ tailWord_2491969).sum := by decide
  have hdescent : baseEnd_2491969 < baseStart_2491969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2491996 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2491996 : Nat := 118140960795 + 2491996 * 2 ^ 59
def prefixEnd_2491996 : Nat := 4983230072969 + 3 ^ 40 * 2491996 * 2
def baseEnd_2491996 : Nat := 1279591737081737287889525

theorem tailTrace_2491996 : CollatzResearch.WordTrace tailWord_2491996 prefixEnd_2491996 1279591737081737287889525 := by
  unfold tailWord_2491996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45445280539965782939119921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60593707386621043918826561 45445280539965782939119921)
  ·
    refine ⟨34083960404974337204339941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45445280539965782939119921 34083960404974337204339941)
    ·
      refine ⟨6390742575932688225813739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34083960404974337204339941 6390742575932688225813739)
      ·
        refine ⟨9586113863899032338720609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390742575932688225813739 9586113863899032338720609)
        ·
          refine ⟨7189585397924274254040457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9586113863899032338720609 7189585397924274254040457)
          ·
            refine ⟨5392189048443205690530343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7189585397924274254040457 5392189048443205690530343)
            ·
              refine ⟨8088283572664808535795515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392189048443205690530343 8088283572664808535795515)
              ·
                refine ⟨12132425358997212803693273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8088283572664808535795515 12132425358997212803693273)
                ·
                  refine ⟨9099319019247909602769955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12132425358997212803693273 9099319019247909602769955)
                  ·
                    refine ⟨13648978528871864404154933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9099319019247909602769955 13648978528871864404154933)
                    ·
                      refine ⟨1279591737081737287889525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13648978528871864404154933 1279591737081737287889525)
                      ·
                        rfl

theorem cell23_2491996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2491996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2491996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2491996 prefixEnd_2491996 := by exact prefixLift 2491996
  have htrace : WordTrace (prefixWord ++ tailWord_2491996) baseStart_2491996 baseEnd_2491996 := by
    simpa [prefixWord, tailWord_2491996, baseEnd_2491996] using wordTrace_append hprefix tailTrace_2491996
  have hstable : (prefixWord ++ tailWord_2491996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2491996).length < 2 ^ (prefixWord ++ tailWord_2491996).sum := by decide
  have hdescent : baseEnd_2491996 < baseStart_2491996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2491996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492009 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_2492009 : Nat := 118140960795 + 2492009 * 2 ^ 59
def prefixEnd_2492009 : Nat := 4983230072969 + 3 ^ 40 * 2492009 * 2
def baseEnd_2492009 : Nat := 1279598412330245737026965

theorem tailTrace_2492009 : CollatzResearch.WordTrace tailWord_2492009 prefixEnd_2492009 1279598412330245737026965 := by
  unfold tailWord_2492009
  simp only [CollatzResearch.WordTrace]
  refine ⟨90891035228884469098463081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60594023485922979398975387 90891035228884469098463081)
  ·
    refine ⟨68168276421663351823847311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90891035228884469098463081 68168276421663351823847311)
    ·
      refine ⟨102252414632495027735770967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68168276421663351823847311 102252414632495027735770967)
      ·
        refine ⟨153378621948742541603656451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102252414632495027735770967 153378621948742541603656451)
        ·
          refine ⟨230067932923113812405484677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153378621948742541603656451 230067932923113812405484677)
          ·
            refine ⟨43137737423083839826028377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230067932923113812405484677 43137737423083839826028377)
            ·
              refine ⟨32353303067312879869521283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43137737423083839826028377 32353303067312879869521283)
              ·
                refine ⟨48529954600969319804281925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32353303067312879869521283 48529954600969319804281925)
                ·
                  refine ⟨9099366487681747463302861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48529954600969319804281925 9099366487681747463302861)
                  ·
                    refine ⟨3412262432880655298738573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9099366487681747463302861 3412262432880655298738573)
                    ·
                      refine ⟨1279598412330245737026965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3412262432880655298738573 1279598412330245737026965)
                      ·
                        rfl

theorem cell23_2492009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_2492009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492009 prefixEnd_2492009 := by exact prefixLift 2492009
  have htrace : WordTrace (prefixWord ++ tailWord_2492009) baseStart_2492009 baseEnd_2492009 := by
    simpa [prefixWord, tailWord_2492009, baseEnd_2492009] using wordTrace_append hprefix tailTrace_2492009
  have hstable : (prefixWord ++ tailWord_2492009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492009).length < 2 ^ (prefixWord ++ tailWord_2492009).sum := by decide
  have hdescent : baseEnd_2492009 < baseStart_2492009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492016 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 7]
def baseStart_2492016 : Nat := 118140960795 + 2492016 * 2 ^ 59
def prefixEnd_2492016 : Nat := 4983230072969 + 3 ^ 40 * 2492016 * 2
def baseEnd_2492016 : Nat := 142178000743869689959937

theorem tailTrace_2492016 : CollatzResearch.WordTrace tailWord_2492016 prefixEnd_2492016 142178000743869689959937 := by
  unfold tailWord_2492016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45445645269929554646983951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60594193693239406195978601 45445645269929554646983951)
  ·
    refine ⟨68168467904894331970475927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45445645269929554646983951 68168467904894331970475927)
    ·
      refine ⟨102252701857341497955713891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68168467904894331970475927 102252701857341497955713891)
      ·
        refine ⟨153379052786012246933570837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102252701857341497955713891 153379052786012246933570837)
        ·
          refine ⟨7189643099344324075011133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153379052786012246933570837 7189643099344324075011133)
          ·
            refine ⟨2696116162254121528129175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7189643099344324075011133 2696116162254121528129175)
            ·
              refine ⟨4044174243381182292193763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696116162254121528129175 4044174243381182292193763)
              ·
                refine ⟨6066261365071773438290645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044174243381182292193763 6066261365071773438290645)
                ·
                  refine ⟨142178000743869689959937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6066261365071773438290645 142178000743869689959937)
                  ·
                    rfl

theorem cell23_2492016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_2492016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492016 prefixEnd_2492016 := by exact prefixLift 2492016
  have htrace : WordTrace (prefixWord ++ tailWord_2492016) baseStart_2492016 baseEnd_2492016 := by
    simpa [prefixWord, tailWord_2492016, baseEnd_2492016] using wordTrace_append hprefix tailTrace_2492016
  have hstable : (prefixWord ++ tailWord_2492016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492016).length < 2 ^ (prefixWord ++ tailWord_2492016).sum := by decide
  have hdescent : baseEnd_2492016 < baseStart_2492016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492046 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2492046 : Nat := 118140960795 + 2492046 * 2 ^ 59
def prefixEnd_2492046 : Nat := 4983230072969 + 3 ^ 40 * 2492046 * 2
def baseEnd_2492046 : Nat := 426539137038154030754765

theorem tailTrace_2492046 : CollatzResearch.WordTrace tailWord_2492046 prefixEnd_2492046 426539137038154030754765 := by
  unfold tailWord_2492046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361548091218803052194999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60594923153166949611706661 11361548091218803052194999)
  ·
    refine ⟨17042322136828204578292499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11361548091218803052194999 17042322136828204578292499)
    ·
      refine ⟨25563483205242306867438749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17042322136828204578292499 25563483205242306867438749)
      ·
        refine ⟨9586306201965865075289531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25563483205242306867438749 9586306201965865075289531)
        ·
          refine ⟨14379459302948797612934297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586306201965865075289531 14379459302948797612934297)
          ·
            refine ⟨10784594477211598209700723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14379459302948797612934297 10784594477211598209700723)
            ·
              refine ⟨16176891715817397314551085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10784594477211598209700723 16176891715817397314551085)
              ·
                refine ⟨6066334393431523992956657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16176891715817397314551085 6066334393431523992956657)
                ·
                  refine ⟨4549750795073642994717493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6066334393431523992956657 4549750795073642994717493)
                  ·
                    refine ⟨426539137038154030754765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4549750795073642994717493 426539137038154030754765)
                    ·
                      rfl

theorem cell23_2492046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2492046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492046 prefixEnd_2492046 := by exact prefixLift 2492046
  have htrace : WordTrace (prefixWord ++ tailWord_2492046) baseStart_2492046 baseEnd_2492046 := by
    simpa [prefixWord, tailWord_2492046, baseEnd_2492046] using wordTrace_append hprefix tailTrace_2492046
  have hstable : (prefixWord ++ tailWord_2492046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492046).length < 2 ^ (prefixWord ++ tailWord_2492046).sum := by decide
  have hdescent : baseEnd_2492046 < baseStart_2492046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492110 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_2492110 : Nat := 118140960795 + 2492110 * 2 ^ 59
def prefixEnd_2492110 : Nat := 4983230072969 + 3 ^ 40 * 2492110 * 2
def baseEnd_2492110 : Nat := 426550091292116613954667

theorem tailTrace_2492110 : CollatzResearch.WordTrace tailWord_2492110 prefixEnd_2492110 426550091292116613954667 := by
  unfold tailWord_2492110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361839875189820418486223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60596479334345708898593189 11361839875189820418486223)
  ·
    refine ⟨17042759812784730627729335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11361839875189820418486223 17042759812784730627729335)
    ·
      refine ⟨25564139719177095941594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17042759812784730627729335 25564139719177095941594003)
      ·
        refine ⟨38346209578765643912391005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25564139719177095941594003 38346209578765643912391005)
        ·
          refine ⟨14379828592037116467146627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38346209578765643912391005 14379828592037116467146627)
          ·
            refine ⟨21569742888055674700719941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14379828592037116467146627 21569742888055674700719941)
            ·
              refine ⟨4044326791510439006384989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21569742888055674700719941 4044326791510439006384989)
              ·
                refine ⟨1516622546816414627394371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4044326791510439006384989 1516622546816414627394371)
                ·
                  refine ⟨2274933820224621941091557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516622546816414627394371 2274933820224621941091557)
                  ·
                    refine ⟨426550091292116613954667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274933820224621941091557 426550091292116613954667)
                    ·
                      rfl

theorem cell23_2492110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_2492110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492110 prefixEnd_2492110 := by exact prefixLift 2492110
  have htrace : WordTrace (prefixWord ++ tailWord_2492110) baseStart_2492110 baseEnd_2492110 := by
    simpa [prefixWord, tailWord_2492110, baseEnd_2492110] using wordTrace_append hprefix tailTrace_2492110
  have hstable : (prefixWord ++ tailWord_2492110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492110).length < 2 ^ (prefixWord ++ tailWord_2492110).sum := by decide
  have hdescent : baseEnd_2492110 < baseStart_2492110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492150 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2492150 : Nat := 118140960795 + 2492150 * 2 ^ 59
def prefixEnd_2492150 : Nat := 4983230072969 + 3 ^ 40 * 2492150 * 2
def baseEnd_2492150 : Nat := 1279670813102529685363817

theorem tailTrace_2492150 : CollatzResearch.WordTrace tailWord_2492150 prefixEnd_2492150 1279670813102529685363817 := by
  unfold tailWord_2492150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681011120085853136209119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60597451947582433452897269 5681011120085853136209119)
  ·
    refine ⟨8521516680128779704313679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5681011120085853136209119 8521516680128779704313679)
    ·
      refine ⟨12782275020193169556470519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8521516680128779704313679 12782275020193169556470519)
      ·
        refine ⟨19173412530289754334705779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12782275020193169556470519 19173412530289754334705779)
        ·
          refine ⟨28760118795434631502058669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19173412530289754334705779 28760118795434631502058669)
          ·
            refine ⟨10785044548287986813272001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28760118795434631502058669 10785044548287986813272001)
            ·
              refine ⟨8088783411215990109954001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10785044548287986813272001 8088783411215990109954001)
              ·
                refine ⟨6066587558411992582465501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8088783411215990109954001 6066587558411992582465501)
                ·
                  refine ⟨2274970334404497218424563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6066587558411992582465501 2274970334404497218424563)
                  ·
                    refine ⟨3412455501606745827636845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2274970334404497218424563 3412455501606745827636845)
                    ·
                      refine ⟨1279670813102529685363817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3412455501606745827636845 1279670813102529685363817)
                      ·
                        rfl

theorem cell23_2492150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2492150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492150 prefixEnd_2492150 := by exact prefixLift 2492150
  have htrace : WordTrace (prefixWord ++ tailWord_2492150) baseStart_2492150 baseEnd_2492150 := by
    simpa [prefixWord, tailWord_2492150, baseEnd_2492150] using wordTrace_append hprefix tailTrace_2492150
  have hstable : (prefixWord ++ tailWord_2492150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492150).length < 2 ^ (prefixWord ++ tailWord_2492150).sum := by decide
  have hdescent : baseEnd_2492150 < baseStart_2492150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492183 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 4, 4]
def baseStart_2492183 : Nat := 118140960795 + 2492183 * 2 ^ 59
def prefixEnd_2492183 : Nat := 4983230072969 + 3 ^ 40 * 2492183 * 2
def baseEnd_2492183 : Nat := 426562585988042685417055

theorem tailTrace_2492183 : CollatzResearch.WordTrace tailWord_2492183 prefixEnd_2492183 426562585988042685417055 := by
  unfold tailWord_2492183
  simp only [CollatzResearch.WordTrace]
  refine ⟨90897381530254096815297203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60598254353502731210198135 90897381530254096815297203)
  ·
    refine ⟨136346072295381145222945805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90897381530254096815297203 136346072295381145222945805)
    ·
      refine ⟨51129777110767929458604677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136346072295381145222945805 51129777110767929458604677)
      ·
        refine ⟨9586833208268986773488377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51129777110767929458604677 9586833208268986773488377)
        ·
          refine ⟨7190124906201740080116283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9586833208268986773488377 7190124906201740080116283)
          ·
            refine ⟨10785187359302610120174425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7190124906201740080116283 10785187359302610120174425)
            ·
              refine ⟨8088890519476957590130819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10785187359302610120174425 8088890519476957590130819)
              ·
                refine ⟨12133335779215436385196229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8088890519476957590130819 12133335779215436385196229)
                ·
                  refine ⟨2275000458602894322224293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12133335779215436385196229 2275000458602894322224293)
                  ·
                    refine ⟨426562585988042685417055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275000458602894322224293 426562585988042685417055)
                    ·
                      rfl

theorem cell23_2492183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_2492183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492183 prefixEnd_2492183 := by exact prefixLift 2492183
  have htrace : WordTrace (prefixWord ++ tailWord_2492183) baseStart_2492183 baseEnd_2492183 := by
    simpa [prefixWord, tailWord_2492183, baseEnd_2492183] using wordTrace_append hprefix tailTrace_2492183
  have hstable : (prefixWord ++ tailWord_2492183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492183).length < 2 ^ (prefixWord ++ tailWord_2492183).sum := by decide
  have hdescent : baseEnd_2492183 < baseStart_2492183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492186 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2492186 : Nat := 118140960795 + 2492186 * 2 ^ 59
def prefixEnd_2492186 : Nat := 4983230072969 + 3 ^ 40 * 2492186 * 2
def baseEnd_2492186 : Nat := 1279689298406091544513651

theorem tailTrace_2492186 : CollatzResearch.WordTrace tailWord_2492186 prefixEnd_2492186 1279689298406091544513651 := by
  unfold tailWord_2492186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724372737310807081914103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60598327299495485551770941 22724372737310807081914103)
  ·
    refine ⟨34086559105966210622871155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22724372737310807081914103 34086559105966210622871155)
    ·
      refine ⟨51129838658949315934306733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34086559105966210622871155 51129838658949315934306733)
      ·
        refine ⟨19173689497105993475365025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51129838658949315934306733 19173689497105993475365025)
        ·
          refine ⟨14380267122829495106523769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19173689497105993475365025 14380267122829495106523769)
          ·
            refine ⟨10785200342122121329892827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14380267122829495106523769 10785200342122121329892827)
            ·
              refine ⟨16177800513183181994839241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10785200342122121329892827 16177800513183181994839241)
              ·
                refine ⟨12133350384887386496129431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16177800513183181994839241 12133350384887386496129431)
                ·
                  refine ⟨18200025577331079744194147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12133350384887386496129431 18200025577331079744194147)
                  ·
                    refine ⟨27300038365996619616291221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18200025577331079744194147 27300038365996619616291221)
                    ·
                      refine ⟨1279689298406091544513651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27300038365996619616291221 1279689298406091544513651)
                      ·
                        rfl

theorem cell23_2492186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2492186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492186 prefixEnd_2492186 := by exact prefixLift 2492186
  have htrace : WordTrace (prefixWord ++ tailWord_2492186) baseStart_2492186 baseEnd_2492186 := by
    simpa [prefixWord, tailWord_2492186, baseEnd_2492186] using wordTrace_append hprefix tailTrace_2492186
  have hstable : (prefixWord ++ tailWord_2492186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492186).length < 2 ^ (prefixWord ++ tailWord_2492186).sum := by decide
  have hdescent : baseEnd_2492186 < baseStart_2492186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492196 : List Nat := [2, 3, 1, 3, 2, 1, 1, 10]
def baseStart_2492196 : Nat := 118140960795 + 2492196 * 2 ^ 59
def prefixEnd_2492196 : Nat := 4983230072969 + 3 ^ 40 * 2492196 * 2
def baseEnd_2492196 : Nat := 47396090118986537236615

theorem tailTrace_2492196 : CollatzResearch.WordTrace tailWord_2492196 prefixEnd_2492196 47396090118986537236615 := by
  unfold tailWord_2492196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45448927839603500017760221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60598570452804666690346961 45448927839603500017760221)
  ·
    refine ⟨17043347939851312506660083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45448927839603500017760221 17043347939851312506660083)
    ·
      refine ⟨25565021909776968759990125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17043347939851312506660083 25565021909776968759990125)
      ·
        refine ⟨9586883216166363284996297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25565021909776968759990125 9586883216166363284996297)
        ·
          refine ⟨7190162412124772463747223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9586883216166363284996297 7190162412124772463747223)
          ·
            refine ⟨10785243618187158695620835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7190162412124772463747223 10785243618187158695620835)
            ·
              refine ⟨16177865427280738043431253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10785243618187158695620835 16177865427280738043431253)
              ·
                refine ⟨47396090118986537236615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16177865427280738043431253 47396090118986537236615)
                ·
                  rfl

theorem cell23_2492196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 10].length) (baseStart_2492196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492196 prefixEnd_2492196 := by exact prefixLift 2492196
  have htrace : WordTrace (prefixWord ++ tailWord_2492196) baseStart_2492196 baseEnd_2492196 := by
    simpa [prefixWord, tailWord_2492196, baseEnd_2492196] using wordTrace_append hprefix tailTrace_2492196
  have hstable : (prefixWord ++ tailWord_2492196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492196).length < 2 ^ (prefixWord ++ tailWord_2492196).sum := by decide
  have hdescent : baseEnd_2492196 < baseStart_2492196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492200 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2492200 : Nat := 118140960795 + 2492200 * 2 ^ 59
def prefixEnd_2492200 : Nat := 4983230072969 + 3 ^ 40 * 2492200 * 2
def baseEnd_2492200 : Nat := 426565495711751496579529

theorem tailTrace_2492200 : CollatzResearch.WordTrace tailWord_2492200 prefixEnd_2492200 426565495711751496579529 := by
  unfold tailWord_2492200
  simp only [CollatzResearch.WordTrace]
  refine ⟨45449000785596254359333027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60598667714128339145777369 45449000785596254359333027)
  ·
    refine ⟨68173501178394381538999541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45449000785596254359333027 68173501178394381538999541)
    ·
      refine ⟨6391265735474473269281207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68173501178394381538999541 6391265735474473269281207)
      ·
        refine ⟨9586898603211709903921811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391265735474473269281207 9586898603211709903921811)
        ·
          refine ⟨14380347904817564855882717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586898603211709903921811 14380347904817564855882717)
          ·
            refine ⟨5392630464306586820956019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14380347904817564855882717 5392630464306586820956019)
            ·
              refine ⟨8088945696459880231434029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392630464306586820956019 8088945696459880231434029)
              ·
                refine ⟨3033354636172455086787761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8088945696459880231434029 3033354636172455086787761)
                ·
                  refine ⟨2275015977129341315090821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3033354636172455086787761 2275015977129341315090821)
                  ·
                    refine ⟨426565495711751496579529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275015977129341315090821 426565495711751496579529)
                    ·
                      rfl

theorem cell23_2492200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2492200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492200 prefixEnd_2492200 := by exact prefixLift 2492200
  have htrace : WordTrace (prefixWord ++ tailWord_2492200) baseStart_2492200 baseEnd_2492200 := by
    simpa [prefixWord, tailWord_2492200, baseEnd_2492200] using wordTrace_append hprefix tailTrace_2492200
  have hstable : (prefixWord ++ tailWord_2492200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492200).length < 2 ^ (prefixWord ++ tailWord_2492200).sum := by decide
  have hdescent : baseEnd_2492200 < baseStart_2492200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492210 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2492210 : Nat := 118140960795 + 2492210 * 2 ^ 59
def prefixEnd_2492210 : Nat := 4983230072969 + 3 ^ 40 * 2492210 * 2
def baseEnd_2492210 : Nat := 1279701621941799450613541

theorem tailTrace_2492210 : CollatzResearch.WordTrace tailWord_2492210 prefixEnd_2492210 1279701621941799450613541 := by
  unfold tailWord_2492210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724591575289070106632521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60598910867437520284353389 22724591575289070106632521)
  ·
    refine ⟨17043443681466802579974391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22724591575289070106632521 17043443681466802579974391)
    ·
      refine ⟨25565165522200203869961587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17043443681466802579974391 25565165522200203869961587)
      ·
        refine ⟨38347748283300305804942381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25565165522200203869961587 38347748283300305804942381)
        ·
          refine ⟨14380405606237614676853393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38347748283300305804942381 14380405606237614676853393)
          ·
            refine ⟨10785304204678211007640045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14380405606237614676853393 10785304204678211007640045)
            ·
              refine ⟨4044489076754329127865017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10785304204678211007640045 4044489076754329127865017)
              ·
                refine ⟨3033366807565746845898763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4044489076754329127865017 3033366807565746845898763)
                ·
                  refine ⟨4550050211348620268848145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033366807565746845898763 4550050211348620268848145)
                  ·
                    refine ⟨3412537658511465201636109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4550050211348620268848145 3412537658511465201636109)
                    ·
                      refine ⟨1279701621941799450613541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3412537658511465201636109 1279701621941799450613541)
                      ·
                        rfl

theorem cell23_2492210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2492210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492210 prefixEnd_2492210 := by exact prefixLift 2492210
  have htrace : WordTrace (prefixWord ++ tailWord_2492210) baseStart_2492210 baseEnd_2492210 := by
    simpa [prefixWord, tailWord_2492210, baseEnd_2492210] using wordTrace_append hprefix tailTrace_2492210
  have hstable : (prefixWord ++ tailWord_2492210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492210).length < 2 ^ (prefixWord ++ tailWord_2492210).sum := by decide
  have hdescent : baseEnd_2492210 < baseStart_2492210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492241 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 1, 2, 2]
def baseStart_2492241 : Nat := 118140960795 + 2492241 * 2 ^ 59
def prefixEnd_2492241 : Nat := 4983230072969 + 3 ^ 40 * 2492241 * 2
def baseEnd_2492241 : Nat := 1279717539842088829325899

theorem tailTrace_2492241 : CollatzResearch.WordTrace tailWord_2492241 prefixEnd_2492241 1279717539842088829325899 := by
  unfold tailWord_2492241
  simp only [CollatzResearch.WordTrace]
  refine ⟨90899496964043972720908577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60599664642695981813939051 90899496964043972720908577)
  ·
    refine ⟨68174622723032979540681433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90899496964043972720908577 68174622723032979540681433)
    ·
      refine ⟨51130967042274734655511075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68174622723032979540681433 51130967042274734655511075)
      ·
        refine ⟨76696450563412101983266613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51130967042274734655511075 76696450563412101983266613)
        ·
          refine ⟨7190292240319884560931245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76696450563412101983266613 7190292240319884560931245)
          ·
            refine ⟨2696359590119956710349217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7190292240319884560931245 2696359590119956710349217)
            ·
              refine ⟨2022269692589967532761913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696359590119956710349217 2022269692589967532761913)
              ·
                refine ⟨1516702269442475649571435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022269692589967532761913 1516702269442475649571435)
                ·
                  refine ⟨2275053404163713474357153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516702269442475649571435 2275053404163713474357153)
                  ·
                    refine ⟨1706290053122785105767865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2275053404163713474357153 1706290053122785105767865)
                    ·
                      refine ⟨1279717539842088829325899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706290053122785105767865 1279717539842088829325899)
                      ·
                        rfl

theorem cell23_2492241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_2492241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492241 prefixEnd_2492241 := by exact prefixLift 2492241
  have htrace : WordTrace (prefixWord ++ tailWord_2492241) baseStart_2492241 baseEnd_2492241 := by
    simpa [prefixWord, tailWord_2492241, baseEnd_2492241] using wordTrace_append hprefix tailTrace_2492241
  have hstable : (prefixWord ++ tailWord_2492241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492241).length < 2 ^ (prefixWord ++ tailWord_2492241).sum := by decide
  have hdescent : baseEnd_2492241 < baseStart_2492241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492256 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_2492256 : Nat := 118140960795 + 2492256 * 2 ^ 59
def prefixEnd_2492256 : Nat := 4983230072969 + 3 ^ 40 * 2492256 * 2
def baseEnd_2492256 : Nat := 426575080683968756879443

theorem tailTrace_2492256 : CollatzResearch.WordTrace tailWord_2492256 prefixEnd_2492256 426575080683968756879443 := by
  unfold tailWord_2492256
  simp only [CollatzResearch.WordTrace]
  refine ⟨45450022029494815141352311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60600029372659753521803081 45450022029494815141352311)
  ·
    refine ⟨68175033044242222712028467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45450022029494815141352311 68175033044242222712028467)
    ·
      refine ⟨102262549566363334068042701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68175033044242222712028467 102262549566363334068042701)
      ·
        refine ⟨38348456087386250275516013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102262549566363334068042701 38348456087386250275516013)
        ·
          refine ⟨14380671032769843853318505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38348456087386250275516013 14380671032769843853318505)
          ·
            refine ⟨10785503274577382889988879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14380671032769843853318505 10785503274577382889988879)
            ·
              refine ⟨16178254911866074334983319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10785503274577382889988879 16178254911866074334983319)
              ·
                refine ⟨24267382367799111502474979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16178254911866074334983319 24267382367799111502474979)
                ·
                  refine ⟨36401073551698667253712469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24267382367799111502474979 36401073551698667253712469)
                  ·
                    refine ⟨426575080683968756879443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36401073551698667253712469 426575080683968756879443)
                    ·
                      rfl

theorem cell23_2492256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_2492256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492256 prefixEnd_2492256 := by exact prefixLift 2492256
  have htrace : WordTrace (prefixWord ++ tailWord_2492256) baseStart_2492256 baseEnd_2492256 := by
    simpa [prefixWord, tailWord_2492256, baseEnd_2492256] using wordTrace_append hprefix tailTrace_2492256
  have hstable : (prefixWord ++ tailWord_2492256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492256).length < 2 ^ (prefixWord ++ tailWord_2492256).sum := by decide
  have hdescent : baseEnd_2492256 < baseStart_2492256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492313 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_2492313 : Nat := 118140960795 + 2492313 * 2 ^ 59
def prefixEnd_2492313 : Nat := 4983230072969 + 3 ^ 40 * 2492313 * 2
def baseEnd_2492313 : Nat := 1279754510449212547625567

theorem tailTrace_2492313 : CollatzResearch.WordTrace tailWord_2492313 prefixEnd_2492313 1279754510449212547625567 := by
  unfold tailWord_2492313
  simp only [CollatzResearch.WordTrace]
  refine ⟨90902123019783129017529593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60601415346522086011686395 90902123019783129017529593)
  ·
    refine ⟨68176592264837346763147195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90902123019783129017529593 68176592264837346763147195)
    ·
      refine ⟨102264888397256020144720793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68176592264837346763147195 102264888397256020144720793)
      ·
        refine ⟨76698666297942015108540595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102264888397256020144720793 76698666297942015108540595)
        ·
          refine ⟨115047999446913022662810893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76698666297942015108540595 115047999446913022662810893)
          ·
            refine ⟨43142999792592383498554085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115047999446913022662810893 43142999792592383498554085)
            ·
              refine ⟨8089312461111071905978891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43142999792592383498554085 8089312461111071905978891)
              ·
                refine ⟨12133968691666607858968337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089312461111071905978891 12133968691666607858968337)
                ·
                  refine ⟨9100476518749955894226253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12133968691666607858968337 9100476518749955894226253)
                  ·
                    refine ⟨3412678694531233460334845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9100476518749955894226253 3412678694531233460334845)
                    ·
                      refine ⟨1279754510449212547625567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3412678694531233460334845 1279754510449212547625567)
                      ·
                        rfl

theorem cell23_2492313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_2492313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492313 prefixEnd_2492313 := by exact prefixLift 2492313
  have htrace : WordTrace (prefixWord ++ tailWord_2492313) baseStart_2492313 baseEnd_2492313 := by
    simpa [prefixWord, tailWord_2492313, baseEnd_2492313] using wordTrace_append hprefix tailTrace_2492313
  have hstable : (prefixWord ++ tailWord_2492313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492313).length < 2 ^ (prefixWord ++ tailWord_2492313).sum := by decide
  have hdescent : baseEnd_2492313 < baseStart_2492313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492334 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2492334 : Nat := 118140960795 + 2492334 * 2 ^ 59
def prefixEnd_2492334 : Nat := 4983230072969 + 3 ^ 40 * 2492334 * 2
def baseEnd_2492334 : Nat := 1279765293542956965462971

theorem tailTrace_2492334 : CollatzResearch.WordTrace tailWord_2492334 prefixEnd_2492334 1279765293542956965462971 := by
  unfold tailWord_2492334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11362861119088381200505507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60601925968471366402696037 11362861119088381200505507)
  ·
    refine ⟨17044291678632571800758261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11362861119088381200505507 17044291678632571800758261)
    ·
      refine ⟨1597902344871803606321087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17044291678632571800758261 1597902344871803606321087)
      ·
        refine ⟨2396853517307705409481631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597902344871803606321087 2396853517307705409481631)
        ·
          refine ⟨3595280275961558114222447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396853517307705409481631 3595280275961558114222447)
          ·
            refine ⟨5392920413942337171333671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595280275961558114222447 5392920413942337171333671)
            ·
              refine ⟨8089380620913505757000507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392920413942337171333671 8089380620913505757000507)
              ·
                refine ⟨12134070931370258635500761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089380620913505757000507 12134070931370258635500761)
                ·
                  refine ⟨9100553198527693976625571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12134070931370258635500761 9100553198527693976625571)
                  ·
                    refine ⟨13650829797791540964938357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9100553198527693976625571 13650829797791540964938357)
                    ·
                      refine ⟨1279765293542956965462971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13650829797791540964938357 1279765293542956965462971)
                      ·
                        rfl

theorem cell23_2492334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2492334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492334 prefixEnd_2492334 := by exact prefixLift 2492334
  have htrace : WordTrace (prefixWord ++ tailWord_2492334) baseStart_2492334 baseEnd_2492334 := by
    simpa [prefixWord, tailWord_2492334, baseEnd_2492334] using wordTrace_append hprefix tailTrace_2492334
  have hstable : (prefixWord ++ tailWord_2492334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492334).length < 2 ^ (prefixWord ++ tailWord_2492334).sum := by decide
  have hdescent : baseEnd_2492334 < baseStart_2492334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492337 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 5]
def baseStart_2492337 : Nat := 118140960795 + 2492337 * 2 ^ 59
def prefixEnd_2492337 : Nat := 4983230072969 + 3 ^ 40 * 2492337 * 2
def baseEnd_2492337 : Nat := 142196314887213383747273

theorem tailTrace_2492337 : CollatzResearch.WordTrace tailWord_2492337 prefixEnd_2492337 142196314887213383747273 := by
  unfold tailWord_2492337
  simp only [CollatzResearch.WordTrace]
  refine ⟨90902998371696181116403265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60601998914464120744268843 90902998371696181116403265)
  ·
    refine ⟨68177248778772135837302449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90902998371696181116403265 68177248778772135837302449)
    ·
      refine ⟨51132936584079101877976837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68177248778772135837302449 51132936584079101877976837)
      ·
        refine ⟨9587425609514831602120657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51132936584079101877976837 9587425609514831602120657)
        ·
          refine ⟨7190569207136123701590493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9587425609514831602120657 7190569207136123701590493)
          ·
            refine ⟨2696463452676046388096435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7190569207136123701590493 2696463452676046388096435)
            ·
              refine ⟨4044695179014069582144653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696463452676046388096435 4044695179014069582144653)
              ·
                refine ⟨1516760692130276093304245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4044695179014069582144653 1516760692130276093304245)
                ·
                  refine ⟨142196314887213383747273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516760692130276093304245 142196314887213383747273)
                  ·
                    rfl

theorem cell23_2492337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 5].length) (baseStart_2492337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492337 prefixEnd_2492337 := by exact prefixLift 2492337
  have htrace : WordTrace (prefixWord ++ tailWord_2492337) baseStart_2492337 baseEnd_2492337 := by
    simpa [prefixWord, tailWord_2492337, baseEnd_2492337] using wordTrace_append hprefix tailTrace_2492337
  have hstable : (prefixWord ++ tailWord_2492337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492337).length < 2 ^ (prefixWord ++ tailWord_2492337).sum := by decide
  have hdescent : baseEnd_2492337 < baseStart_2492337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492350 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2492350 : Nat := 118140960795 + 2492350 * 2 ^ 59
def prefixEnd_2492350 : Nat := 4983230072969 + 3 ^ 40 * 2492350 * 2
def baseEnd_2492350 : Nat := 426591169744476300954299

theorem tailTrace_2492350 : CollatzResearch.WordTrace tailWord_2492350 prefixEnd_2492350 426591169744476300954299 := by
  unfold tailWord_2492350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11362934065081135542078313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60602315013766056224417669 11362934065081135542078313)
  ·
    refine ⟨8522200548810851656558735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11362934065081135542078313 8522200548810851656558735)
    ·
      refine ⟨12783300823216277484838103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522200548810851656558735 12783300823216277484838103)
      ·
        refine ⟨19174951234824416227257155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12783300823216277484838103 19174951234824416227257155)
        ·
          refine ⟨28762426852236624340885733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19174951234824416227257155 28762426852236624340885733)
          ·
            refine ⟨5392955034794367063916075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28762426852236624340885733 5392955034794367063916075)
            ·
              refine ⟨8089432552191550595874113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392955034794367063916075 8089432552191550595874113)
              ·
                refine ⟨6067074414143662946905585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089432552191550595874113 6067074414143662946905585)
                ·
                  refine ⟨4550305810607747210179189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067074414143662946905585 4550305810607747210179189)
                  ·
                    refine ⟨426591169744476300954299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4550305810607747210179189 426591169744476300954299)
                    ·
                      rfl

theorem cell23_2492350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2492350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492350 prefixEnd_2492350 := by exact prefixLift 2492350
  have htrace : WordTrace (prefixWord ++ tailWord_2492350) baseStart_2492350 baseEnd_2492350 := by
    simpa [prefixWord, tailWord_2492350, baseEnd_2492350] using wordTrace_append hprefix tailTrace_2492350
  have hstable : (prefixWord ++ tailWord_2492350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492350).length < 2 ^ (prefixWord ++ tailWord_2492350).sum := by decide
  have hdescent : baseEnd_2492350 < baseStart_2492350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492440 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_2492440 : Nat := 118140960795 + 2492440 * 2 ^ 59
def prefixEnd_2492440 : Nat := 4983230072969 + 3 ^ 40 * 2492440 * 2
def baseEnd_2492440 : Nat := 426606574164111183579161

theorem tailTrace_2492440 : CollatzResearch.WordTrace tailWord_2492440 prefixEnd_2492440 426606574164111183579161 := by
  unfold tailWord_2492440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45453377545161514853701387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60604503393548686471601849 45453377545161514853701387)
  ·
    refine ⟨68180066317742272280552081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45453377545161514853701387 68180066317742272280552081)
    ·
      refine ⟨51135049738306704210414061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68180066317742272280552081 51135049738306704210414061)
      ·
        refine ⟨19175643651865014078905273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51135049738306704210414061 19175643651865014078905273)
        ·
          refine ⟨14381732738898760559178955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19175643651865014078905273 14381732738898760559178955)
          ·
            refine ⟨21572599108348140838768433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14381732738898760559178955 21572599108348140838768433)
            ·
              refine ⟨16179449331261105629076325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21572599108348140838768433 16179449331261105629076325)
              ·
                refine ⟨3033646749611457305451811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16179449331261105629076325 3033646749611457305451811)
                ·
                  refine ⟨4550470124417185958177717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033646749611457305451811 4550470124417185958177717)
                  ·
                    refine ⟨426606574164111183579161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4550470124417185958177717 426606574164111183579161)
                    ·
                      rfl

theorem cell23_2492440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_2492440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492440 prefixEnd_2492440 := by exact prefixLift 2492440
  have htrace : WordTrace (prefixWord ++ tailWord_2492440) baseStart_2492440 baseEnd_2492440 := by
    simpa [prefixWord, tailWord_2492440, baseEnd_2492440] using wordTrace_append hprefix tailTrace_2492440
  have hstable : (prefixWord ++ tailWord_2492440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492440).length < 2 ^ (prefixWord ++ tailWord_2492440).sum := by decide
  have hdescent : baseEnd_2492440 < baseStart_2492440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492480 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_2492480 : Nat := 118140960795 + 2492480 * 2 ^ 59
def prefixEnd_2492480 : Nat := 4983230072969 + 3 ^ 40 * 2492480 * 2
def baseEnd_2492480 : Nat := 1279840261718513394237299

theorem tailTrace_2492480 : CollatzResearch.WordTrace tailWord_2492480 prefixEnd_2492480 1279840261718513394237299 := by
  unfold tailWord_2492480
  simp only [CollatzResearch.WordTrace]
  refine ⟨45454107005089058269429447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60605476006785411025905929 45454107005089058269429447)
  ·
    refine ⟨68181160507633587404144171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45454107005089058269429447 68181160507633587404144171)
    ·
      refine ⟨102271740761450381106216257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68181160507633587404144171 102271740761450381106216257)
      ·
        refine ⟨76703805571087785829662193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102271740761450381106216257 76703805571087785829662193)
        ·
          refine ⟨57527854178315839372246645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76703805571087785829662193 57527854178315839372246645)
          ·
            refine ⟨5393236329217109941148123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57527854178315839372246645 5393236329217109941148123)
            ·
              refine ⟨8089854493825664911722185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393236329217109941148123 8089854493825664911722185)
              ·
                refine ⟨6067390870369248683791639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089854493825664911722185 6067390870369248683791639)
                ·
                  refine ⟨9101086305553873025687459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067390870369248683791639 9101086305553873025687459)
                  ·
                    refine ⟨13651629458330809538531189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9101086305553873025687459 13651629458330809538531189)
                    ·
                      refine ⟨1279840261718513394237299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13651629458330809538531189 1279840261718513394237299)
                      ·
                        rfl

theorem cell23_2492480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_2492480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492480 prefixEnd_2492480 := by exact prefixLift 2492480
  have htrace : WordTrace (prefixWord ++ tailWord_2492480) baseStart_2492480 baseEnd_2492480 := by
    simpa [prefixWord, tailWord_2492480, baseEnd_2492480] using wordTrace_append hprefix tailTrace_2492480
  have hstable : (prefixWord ++ tailWord_2492480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492480).length < 2 ^ (prefixWord ++ tailWord_2492480).sum := by decide
  have hdescent : baseEnd_2492480 < baseStart_2492480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492494 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_2492494 : Nat := 118140960795 + 2492494 * 2 ^ 59
def prefixEnd_2492494 : Nat := 4983230072969 + 3 ^ 40 * 2492494 * 2
def baseEnd_2492494 : Nat := 1279847450447676339462235

theorem tailTrace_2492494 : CollatzResearch.WordTrace tailWord_2492494 prefixEnd_2492494 1279847450447676339462235 := by
  unfold tailWord_2492494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363590579015924616233567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60605816421418264619912357 11363590579015924616233567)
  ·
    refine ⟨17045385868523886924350351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11363590579015924616233567 17045385868523886924350351)
    ·
      refine ⟨25568078802785830386525527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17045385868523886924350351 25568078802785830386525527)
      ·
        refine ⟨38352118204178745579788291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25568078802785830386525527 38352118204178745579788291)
        ·
          refine ⟨57528177306268118369682437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38352118204178745579788291 57528177306268118369682437)
          ·
            refine ⟨10786533244925272194315457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57528177306268118369682437 10786533244925272194315457)
            ·
              refine ⟨8089899933693954145736593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786533244925272194315457 8089899933693954145736593)
              ·
                refine ⟨6067424950270465609302445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089899933693954145736593 6067424950270465609302445)
                ·
                  refine ⟨2275284356351424603488417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6067424950270465609302445 2275284356351424603488417)
                  ·
                    refine ⟨1706463267263568452616313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2275284356351424603488417 1706463267263568452616313)
                    ·
                      refine ⟨1279847450447676339462235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706463267263568452616313 1279847450447676339462235)
                      ·
                        rfl

theorem cell23_2492494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_2492494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492494 prefixEnd_2492494 := by exact prefixLift 2492494
  have htrace : WordTrace (prefixWord ++ tailWord_2492494) baseStart_2492494 baseEnd_2492494 := by
    simpa [prefixWord, tailWord_2492494, baseEnd_2492494] using wordTrace_append hprefix tailTrace_2492494
  have hstable : (prefixWord ++ tailWord_2492494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492494).length < 2 ^ (prefixWord ++ tailWord_2492494).sum := by decide
  have hdescent : baseEnd_2492494 < baseStart_2492494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492513 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2492513 : Nat := 118140960795 + 2492513 * 2 ^ 59
def prefixEnd_2492513 : Nat := 4983230072969 + 3 ^ 40 * 2492513 * 2
def baseEnd_2492513 : Nat := 426619068860037255041549

theorem tailTrace_2492513 : CollatzResearch.WordTrace tailWord_2492513 prefixEnd_2492513 426619068860037255041549 := by
  unfold tailWord_2492513
  simp only [CollatzResearch.WordTrace]
  refine ⟨90909417619058563174810193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60606278412705708783206795 90909417619058563174810193)
  ·
    refine ⟨68182063214293922381107645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90909417619058563174810193 68182063214293922381107645)
    ·
      refine ⟨25568273705360220892915367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68182063214293922381107645 25568273705360220892915367)
      ·
        refine ⟨38352410558040331339373051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25568273705360220892915367 38352410558040331339373051)
        ·
          refine ⟨57528615837060497009059577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38352410558040331339373051 57528615837060497009059577)
          ·
            refine ⟨43146461877795372756794683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57528615837060497009059577 43146461877795372756794683)
            ·
              refine ⟨64719692816693059135192025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43146461877795372756794683 64719692816693059135192025)
              ·
                refine ⟨48539769612519794351394019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64719692816693059135192025 48539769612519794351394019)
                ·
                  refine ⟨72809654418779691527091029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48539769612519794351394019 72809654418779691527091029)
                  ·
                    refine ⟨426619068860037255041549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72809654418779691527091029 426619068860037255041549)
                    ·
                      rfl

theorem cell23_2492513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2492513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492513 prefixEnd_2492513 := by exact prefixLift 2492513
  have htrace : WordTrace (prefixWord ++ tailWord_2492513) baseStart_2492513 baseEnd_2492513 := by
    simpa [prefixWord, tailWord_2492513, baseEnd_2492513] using wordTrace_append hprefix tailTrace_2492513
  have hstable : (prefixWord ++ tailWord_2492513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492513).length < 2 ^ (prefixWord ++ tailWord_2492513).sum := by decide
  have hdescent : baseEnd_2492513 < baseStart_2492513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492514 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2492514 : Nat := 118140960795 + 2492514 * 2 ^ 59
def prefixEnd_2492514 : Nat := 4983230072969 + 3 ^ 40 * 2492514 * 2
def baseEnd_2492514 : Nat := 1279857720060766261212143

theorem tailTrace_2492514 : CollatzResearch.WordTrace tailWord_2492514 prefixEnd_2492514 1279857720060766261212143 := by
  unfold tailWord_2492514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727363523013735086399149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60606302728036626897064397 22727363523013735086399149)
  ·
    refine ⟨8522761321130150657399681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22727363523013735086399149 8522761321130150657399681)
    ·
      refine ⟨6392070990847612993049761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8522761321130150657399681 6392070990847612993049761)
      ·
        refine ⟨4794053243135709744787321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6392070990847612993049761 4794053243135709744787321)
        ·
          refine ⟨3595539932351782308590491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4794053243135709744787321 3595539932351782308590491)
          ·
            refine ⟨5393309898527673462885737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595539932351782308590491 5393309898527673462885737)
            ·
              refine ⟨4044982423895755097164303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393309898527673462885737 4044982423895755097164303)
              ·
                refine ⟨6067473635843632645746455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044982423895755097164303 6067473635843632645746455)
                ·
                  refine ⟨9101210453765448968619683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067473635843632645746455 9101210453765448968619683)
                  ·
                    refine ⟨13651815680648173452929525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9101210453765448968619683 13651815680648173452929525)
                    ·
                      refine ⟨1279857720060766261212143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13651815680648173452929525 1279857720060766261212143)
                      ·
                        rfl

theorem cell23_2492514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2492514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492514 prefixEnd_2492514 := by exact prefixLift 2492514
  have htrace : WordTrace (prefixWord ++ tailWord_2492514) baseStart_2492514 baseEnd_2492514 := by
    simpa [prefixWord, tailWord_2492514, baseEnd_2492514] using wordTrace_append hprefix tailTrace_2492514
  have hstable : (prefixWord ++ tailWord_2492514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492514).length < 2 ^ (prefixWord ++ tailWord_2492514).sum := by decide
  have hdescent : baseEnd_2492514 < baseStart_2492514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492527 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 3]
def baseStart_2492527 : Nat := 118140960795 + 2492527 * 2 ^ 59
def prefixEnd_2492527 : Nat := 4983230072969 + 3 ^ 40 * 2492527 * 2
def baseEnd_2492527 : Nat := 1279864395309274710349583

theorem tailTrace_2492527 : CollatzResearch.WordTrace tailWord_2492527 prefixEnd_2492527 1279864395309274710349583 := by
  unfold tailWord_2492527
  simp only [CollatzResearch.WordTrace]
  refine ⟨90909928241007843565819835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60606618827338562377213223 90909928241007843565819835)
  ·
    refine ⟨136364892361511765348729753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90909928241007843565819835 136364892361511765348729753)
    ·
      refine ⟨102273669271133824011547315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136364892361511765348729753 102273669271133824011547315)
      ·
        refine ⟨153410503906700736017320973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102273669271133824011547315 153410503906700736017320973)
        ·
          refine ⟨57528938965012776006495365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153410503906700736017320973 57528938965012776006495365)
          ·
            refine ⟨10786676055939895501217881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57528938965012776006495365 10786676055939895501217881)
            ·
              refine ⟨8090007041954921625913411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786676055939895501217881 8090007041954921625913411)
              ·
                refine ⟨12135010562932382438870117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090007041954921625913411 12135010562932382438870117)
                ·
                  refine ⟨2275314480549821707288147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12135010562932382438870117 2275314480549821707288147)
                  ·
                    refine ⟨3412971720824732560932221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2275314480549821707288147 3412971720824732560932221)
                    ·
                      refine ⟨1279864395309274710349583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3412971720824732560932221 1279864395309274710349583)
                      ·
                        rfl

theorem cell23_2492527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_2492527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492527 prefixEnd_2492527 := by exact prefixLift 2492527
  have htrace : WordTrace (prefixWord ++ tailWord_2492527) baseStart_2492527 baseEnd_2492527 := by
    simpa [prefixWord, tailWord_2492527, baseEnd_2492527] using wordTrace_append hprefix tailTrace_2492527
  have hstable : (prefixWord ++ tailWord_2492527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492527).length < 2 ^ (prefixWord ++ tailWord_2492527).sum := by decide
  have hdescent : baseEnd_2492527 < baseStart_2492527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492528 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 1, 2, 2]
def baseStart_2492528 : Nat := 118140960795 + 2492528 * 2 ^ 59
def prefixEnd_2492528 : Nat := 4983230072969 + 3 ^ 40 * 2492528 * 2
def baseEnd_2492528 : Nat := 1279864908789929206437079

theorem tailTrace_2492528 : CollatzResearch.WordTrace tailWord_2492528 prefixEnd_2492528 1279864908789929206437079 := by
  unfold tailWord_2492528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45454982357002110368303119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60606643142669480491070825 45454982357002110368303119)
  ·
    refine ⟨68182473535503165552454679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45454982357002110368303119 68182473535503165552454679)
    ·
      refine ⟨102273710303254748328682019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68182473535503165552454679 102273710303254748328682019)
      ·
        refine ⟨153410565454882122493023029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102273710303254748328682019 153410565454882122493023029)
        ·
          refine ⟨14382240511395198983720909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153410565454882122493023029 14382240511395198983720909)
          ·
            refine ⟨5393340191773199618895341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14382240511395198983720909 5393340191773199618895341)
            ·
              refine ⟨2022502571914949857085753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5393340191773199618895341 2022502571914949857085753)
              ·
                refine ⟨1516876928936212392814315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022502571914949857085753 1516876928936212392814315)
                ·
                  refine ⟨2275315393404318589221473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516876928936212392814315 2275315393404318589221473)
                  ·
                    refine ⟨1706486545053238941916105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2275315393404318589221473 1706486545053238941916105)
                    ·
                      refine ⟨1279864908789929206437079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706486545053238941916105 1279864908789929206437079)
                      ·
                        rfl

theorem cell23_2492528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 2, 2].length) (baseStart_2492528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492528 prefixEnd_2492528 := by exact prefixLift 2492528
  have htrace : WordTrace (prefixWord ++ tailWord_2492528) baseStart_2492528 baseEnd_2492528 := by
    simpa [prefixWord, tailWord_2492528, baseEnd_2492528] using wordTrace_append hprefix tailTrace_2492528
  have hstable : (prefixWord ++ tailWord_2492528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492528).length < 2 ^ (prefixWord ++ tailWord_2492528).sum := by decide
  have hdescent : baseEnd_2492528 < baseStart_2492528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492554 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_2492554 : Nat := 118140960795 + 2492554 * 2 ^ 59
def prefixEnd_2492554 : Nat := 4983230072969 + 3 ^ 40 * 2492554 * 2
def baseEnd_2492554 : Nat := 1279878259286946104711959

theorem tailTrace_2492554 : CollatzResearch.WordTrace tailWord_2492554 prefixEnd_2492554 1279878259286946104711959 := by
  unfold tailWord_2492554
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727728252977506794263179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60607275341273351451368477 22727728252977506794263179)
  ·
    refine ⟨34091592379466260191394769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22727728252977506794263179 34091592379466260191394769)
    ·
      refine ⟨25568694284599695143546077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34091592379466260191394769 25568694284599695143546077)
      ·
        refine ⟨9588260356724885678829779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25568694284599695143546077 9588260356724885678829779)
        ·
          refine ⟨14382390535087328518244669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9588260356724885678829779 14382390535087328518244669)
          ·
            refine ⟨5393396450657748194341751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14382390535087328518244669 5393396450657748194341751)
            ·
              refine ⟨8090094675986622291512627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393396450657748194341751 8090094675986622291512627)
              ·
                refine ⟨12135142013979933437268941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090094675986622291512627 12135142013979933437268941)
                ·
                  refine ⟨4550678255242475038975853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12135142013979933437268941 4550678255242475038975853)
                  ·
                    refine ⟨1706504345715928139615945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4550678255242475038975853 1706504345715928139615945)
                    ·
                      refine ⟨1279878259286946104711959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706504345715928139615945 1279878259286946104711959)
                      ·
                        rfl

theorem cell23_2492554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_2492554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492554 prefixEnd_2492554 := by exact prefixLift 2492554
  have htrace : WordTrace (prefixWord ++ tailWord_2492554) baseStart_2492554 baseEnd_2492554 := by
    simpa [prefixWord, tailWord_2492554, baseEnd_2492554] using wordTrace_append hprefix tailTrace_2492554
  have hstable : (prefixWord ++ tailWord_2492554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492554).length < 2 ^ (prefixWord ++ tailWord_2492554).sum := by decide
  have hdescent : baseEnd_2492554 < baseStart_2492554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492674 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2492674 : Nat := 118140960795 + 2492674 * 2 ^ 59
def prefixEnd_2492674 : Nat := 4983230072969 + 3 ^ 40 * 2492674 * 2
def baseEnd_2492674 : Nat := 1279939876965485635211407

theorem tailTrace_2492674 : CollatzResearch.WordTrace tailWord_2492674 prefixEnd_2492674 1279939876965485635211407 := by
  unfold tailWord_2492674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728822442868821917855269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60610193180983525114280717 22728822442868821917855269)
  ·
    refine ⟨4261654208037904109597863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22728822442868821917855269 4261654208037904109597863)
    ·
      refine ⟨6392481312056856164396795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261654208037904109597863 6392481312056856164396795)
      ·
        refine ⟨9588721968085284246595193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392481312056856164396795 9588721968085284246595193)
        ·
          refine ⟨7191541476063963184946395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9588721968085284246595193 7191541476063963184946395)
          ·
            refine ⟨10787312214095944777419593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191541476063963184946395 10787312214095944777419593)
            ·
              refine ⟨8090484160571958583064695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10787312214095944777419593 8090484160571958583064695)
              ·
                refine ⟨12135726240857937874597043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090484160571958583064695 12135726240857937874597043)
                ·
                  refine ⟨18203589361286906811895565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12135726240857937874597043 18203589361286906811895565)
                  ·
                    refine ⟨6826346010482590054460837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18203589361286906811895565 6826346010482590054460837)
                    ·
                      refine ⟨1279939876965485635211407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6826346010482590054460837 1279939876965485635211407)
                      ·
                        rfl

theorem cell23_2492674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2492674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492674 prefixEnd_2492674 := by exact prefixLift 2492674
  have htrace : WordTrace (prefixWord ++ tailWord_2492674) baseStart_2492674 baseEnd_2492674 := by
    simpa [prefixWord, tailWord_2492674, baseEnd_2492674] using wordTrace_append hprefix tailTrace_2492674
  have hstable : (prefixWord ++ tailWord_2492674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492674).length < 2 ^ (prefixWord ++ tailWord_2492674).sum := by decide
  have hdescent : baseEnd_2492674 < baseStart_2492674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492720 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_2492720 : Nat := 118140960795 + 2492720 * 2 ^ 59
def prefixEnd_2492720 : Nat := 4983230072969 + 3 ^ 40 * 2492720 * 2
def baseEnd_2492720 : Nat := 1279963497075592455236195

theorem tailTrace_2492720 : CollatzResearch.WordTrace tailWord_2492720 prefixEnd_2492720 1279963497075592455236195 := by
  unfold tailWord_2492720
  simp only [CollatzResearch.WordTrace]
  refine ⟨45458483764654318763797807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60611311686205758351730409 45458483764654318763797807)
  ·
    refine ⟨68187725646981478145696711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45458483764654318763797807 68187725646981478145696711)
    ·
      refine ⟨102281588470472217218545067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68187725646981478145696711 102281588470472217218545067)
      ·
        refine ⟨153422382705708325827817601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102281588470472217218545067 153422382705708325827817601)
        ·
          refine ⟨115066787029281244370863201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153422382705708325827817601 115066787029281244370863201)
          ·
            refine ⟨86300090271960933278147401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115066787029281244370863201 86300090271960933278147401)
            ·
              refine ⟨64725067703970699958610551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86300090271960933278147401 64725067703970699958610551)
              ·
                refine ⟨97087601555956049937915827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64725067703970699958610551 97087601555956049937915827)
                ·
                  refine ⟨145631402333934074906873741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97087601555956049937915827 145631402333934074906873741)
                  ·
                    refine ⟨54611775875225278090077653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145631402333934074906873741 54611775875225278090077653)
                    ·
                      refine ⟨1279963497075592455236195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54611775875225278090077653 1279963497075592455236195)
                      ·
                        rfl

theorem cell23_2492720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_2492720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492720 prefixEnd_2492720 := by exact prefixLift 2492720
  have htrace : WordTrace (prefixWord ++ tailWord_2492720) baseStart_2492720 baseEnd_2492720 := by
    simpa [prefixWord, tailWord_2492720, baseEnd_2492720] using wordTrace_append hprefix tailTrace_2492720
  have hstable : (prefixWord ++ tailWord_2492720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492720).length < 2 ^ (prefixWord ++ tailWord_2492720).sum := by decide
  have hdescent : baseEnd_2492720 < baseStart_2492720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492767 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_2492767 : Nat := 118140960795 + 2492767 * 2 ^ 59
def prefixEnd_2492767 : Nat := 4983230072969 + 3 ^ 40 * 2492767 * 2
def baseEnd_2492767 : Nat := 1279987630666353771348479

theorem tailTrace_2492767 : CollatzResearch.WordTrace tailWord_2492767 prefixEnd_2492767 1279987630666353771348479 := by
  unfold tailWord_2492767
  simp only [CollatzResearch.WordTrace]
  refine ⟨90918681760138364554556555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60612454506758909703037703 90918681760138364554556555)
  ·
    refine ⟨136378022640207546831834833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90918681760138364554556555 136378022640207546831834833)
    ·
      refine ⟨102283516980155660123876125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136378022640207546831834833 102283516980155660123876125)
      ·
        refine ⟨38356318867558372546453547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102283516980155660123876125 38356318867558372546453547)
        ·
          refine ⟨57534478301337558819680321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38356318867558372546453547 57534478301337558819680321)
          ·
            refine ⟨43150858726003169114760241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57534478301337558819680321 43150858726003169114760241)
            ·
              refine ⟨32363144044502376836070181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43150858726003169114760241 32363144044502376836070181)
              ·
                refine ⟨6068089508344195656763159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32363144044502376836070181 6068089508344195656763159)
                ·
                  refine ⟨9102134262516293485144739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068089508344195656763159 9102134262516293485144739)
                  ·
                    refine ⟨13653201393774440227717109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9102134262516293485144739 13653201393774440227717109)
                    ·
                      refine ⟨1279987630666353771348479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13653201393774440227717109 1279987630666353771348479)
                      ·
                        rfl

theorem cell23_2492767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_2492767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492767 prefixEnd_2492767 := by exact prefixLift 2492767
  have htrace : WordTrace (prefixWord ++ tailWord_2492767) baseStart_2492767 baseEnd_2492767 := by
    simpa [prefixWord, tailWord_2492767, baseEnd_2492767] using wordTrace_append hprefix tailTrace_2492767
  have hstable : (prefixWord ++ tailWord_2492767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492767).length < 2 ^ (prefixWord ++ tailWord_2492767).sum := by decide
  have hdescent : baseEnd_2492767 < baseStart_2492767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492784 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_2492784 : Nat := 118140960795 + 2492784 * 2 ^ 59
def prefixEnd_2492784 : Nat := 4983230072969 + 3 ^ 40 * 2492784 * 2
def baseEnd_2492784 : Nat := 1279996359837480204835901

theorem tailTrace_2492784 : CollatzResearch.WordTrace tailWord_2492784 prefixEnd_2492784 1279996359837480204835901 := by
  unfold tailWord_2492784
  simp only [CollatzResearch.WordTrace]
  refine ⟨45459650900538388228962703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60612867867384517638616937 45459650900538388228962703)
  ·
    refine ⟨68189476350807582343444055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45459650900538388228962703 68189476350807582343444055)
    ·
      refine ⟨102284214526211373515166083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68189476350807582343444055 102284214526211373515166083)
      ·
        refine ⟨153426321789317060272749125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102284214526211373515166083 153426321789317060272749125)
        ·
          refine ⟨28767435335496948801140461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153426321789317060272749125 28767435335496948801140461)
          ·
            refine ⟨10787788250811355800427673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28767435335496948801140461 10787788250811355800427673)
            ·
              refine ⟨8090841188108516850320755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10787788250811355800427673 8090841188108516850320755)
              ·
                refine ⟨12136261782162775275481133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090841188108516850320755 12136261782162775275481133)
                ·
                  refine ⟨4551098168311040728305425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12136261782162775275481133 4551098168311040728305425)
                  ·
                    refine ⟨3413323626233280546229069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551098168311040728305425 3413323626233280546229069)
                    ·
                      refine ⟨1279996359837480204835901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3413323626233280546229069 1279996359837480204835901)
                      ·
                        rfl

theorem cell23_2492784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_2492784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492784 prefixEnd_2492784 := by exact prefixLift 2492784
  have htrace : WordTrace (prefixWord ++ tailWord_2492784) baseStart_2492784 baseEnd_2492784 := by
    simpa [prefixWord, tailWord_2492784, baseEnd_2492784] using wordTrace_append hprefix tailTrace_2492784
  have hstable : (prefixWord ++ tailWord_2492784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492784).length < 2 ^ (prefixWord ++ tailWord_2492784).sum := by decide
  have hdescent : baseEnd_2492784 < baseStart_2492784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492874 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_2492874 : Nat := 118140960795 + 2492874 * 2 ^ 59
def prefixEnd_2492874 : Nat := 4983230072969 + 3 ^ 40 * 2492874 * 2
def baseEnd_2492874 : Nat := 1280042573096384852710487

theorem tailTrace_2492874 : CollatzResearch.WordTrace tailWord_2492874 prefixEnd_2492874 1280042573096384852710487 := by
  unfold tailWord_2492874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22730646092687680457175419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60615056247167147885801117 22730646092687680457175419)
  ·
    refine ⟨34095969139031520685763129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22730646092687680457175419 34095969139031520685763129)
    ·
      refine ⟨25571976854273640514322347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34095969139031520685763129 25571976854273640514322347)
      ·
        refine ⟨38357965281410460771483521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25571976854273640514322347 38357965281410460771483521)
        ·
          refine ⟨28768473961057845578612641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38357965281410460771483521 28768473961057845578612641)
          ·
            refine ⟨21576355470793384183959481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28768473961057845578612641 21576355470793384183959481)
            ·
              refine ⟨16182266603095038137969611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21576355470793384183959481 16182266603095038137969611)
              ·
                refine ⟨24273399904642557206954417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16182266603095038137969611 24273399904642557206954417)
                ·
                  refine ⟨18205049928481917905215813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24273399904642557206954417 18205049928481917905215813)
                  ·
                    refine ⟨3413446861590359607227965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18205049928481917905215813 3413446861590359607227965)
                    ·
                      refine ⟨1280042573096384852710487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3413446861590359607227965 1280042573096384852710487)
                      ·
                        rfl

theorem cell23_2492874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_2492874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492874 prefixEnd_2492874 := by exact prefixLift 2492874
  have htrace : WordTrace (prefixWord ++ tailWord_2492874) baseStart_2492874 baseEnd_2492874 := by
    simpa [prefixWord, tailWord_2492874, baseEnd_2492874] using wordTrace_append hprefix tailTrace_2492874
  have hstable : (prefixWord ++ tailWord_2492874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492874).length < 2 ^ (prefixWord ++ tailWord_2492874).sum := by decide
  have hdescent : baseEnd_2492874 < baseStart_2492874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492961 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2492961 : Nat := 118140960795 + 2492961 * 2 ^ 59
def prefixEnd_2492961 : Nat := 4983230072969 + 3 ^ 40 * 2492961 * 2
def baseEnd_2492961 : Nat := 1280087245913326012322587

theorem tailTrace_2492961 : CollatzResearch.WordTrace tailWord_2492961 prefixEnd_2492961 1280087245913326012322587 := by
  unfold tailWord_2492961
  simp only [CollatzResearch.WordTrace]
  refine ⟨90925757521435535687118737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60617171680957023791412491 90925757521435535687118737)
  ·
    refine ⟨68194318141076651765339053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90925757521435535687118737 68194318141076651765339053)
    ·
      refine ⟨25572869302903744412002145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68194318141076651765339053 25572869302903744412002145)
      ·
        refine ⟨19179651977177808309001609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25572869302903744412002145 19179651977177808309001609)
        ·
          refine ⟨14384738982883356231751207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19179651977177808309001609 14384738982883356231751207)
          ·
            refine ⟨21577108474325034347626811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14384738982883356231751207 21577108474325034347626811)
            ·
              refine ⟨32365662711487551521440217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21577108474325034347626811 32365662711487551521440217)
              ·
                refine ⟨24274247033615663641080163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32365662711487551521440217 24274247033615663641080163)
                ·
                  refine ⟨36411370550423495461620245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24274247033615663641080163 36411370550423495461620245)
                  ·
                    refine ⟨1706782994551101349763449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36411370550423495461620245 1706782994551101349763449)
                    ·
                      refine ⟨1280087245913326012322587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706782994551101349763449 1280087245913326012322587)
                      ·
                        rfl

theorem cell23_2492961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2492961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492961 prefixEnd_2492961 := by exact prefixLift 2492961
  have htrace : WordTrace (prefixWord ++ tailWord_2492961) baseStart_2492961 baseEnd_2492961 := by
    simpa [prefixWord, tailWord_2492961, baseEnd_2492961] using wordTrace_append hprefix tailTrace_2492961
  have hstable : (prefixWord ++ tailWord_2492961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492961).length < 2 ^ (prefixWord ++ tailWord_2492961).sum := by decide
  have hdescent : baseEnd_2492961 < baseStart_2492961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492973 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2492973 : Nat := 118140960795 + 2492973 * 2 ^ 59
def prefixEnd_2492973 : Nat := 4983230072969 + 3 ^ 40 * 2492973 * 2
def baseEnd_2492973 : Nat := 1280093407681179965372533

theorem tailTrace_2492973 : CollatzResearch.WordTrace tailWord_2492973 prefixEnd_2492973 1280093407681179965372533 := by
  unfold tailWord_2492973
  simp only [CollatzResearch.WordTrace]
  refine ⟨90926195197392061736555573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60617463464928041157703715 90926195197392061736555573)
  ·
    refine ⟨8524330799755505787802085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90926195197392061736555573 8524330799755505787802085)
    ·
      refine ⟨1598312024954157335212891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8524330799755505787802085 1598312024954157335212891)
      ·
        refine ⟨2397468037431236002819337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598312024954157335212891 2397468037431236002819337)
        ·
          refine ⟨1798101028073427002114503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397468037431236002819337 1798101028073427002114503)
          ·
            refine ⟨2697151542110140503171755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798101028073427002114503 2697151542110140503171755)
            ·
              refine ⟨4045727313165210754757633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697151542110140503171755 4045727313165210754757633)
              ·
                refine ⟨3034295484873908066068225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4045727313165210754757633 3034295484873908066068225)
                ·
                  refine ⟨2275721613655431049551169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034295484873908066068225 2275721613655431049551169)
                  ·
                    refine ⟨1706791210241573287163377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2275721613655431049551169 1706791210241573287163377)
                    ·
                      refine ⟨1280093407681179965372533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706791210241573287163377 1280093407681179965372533)
                      ·
                        rfl

theorem cell23_2492973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2492973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492973 prefixEnd_2492973 := by exact prefixLift 2492973
  have htrace : WordTrace (prefixWord ++ tailWord_2492973) baseStart_2492973 baseEnd_2492973 := by
    simpa [prefixWord, tailWord_2492973, baseEnd_2492973] using wordTrace_append hprefix tailTrace_2492973
  have hstable : (prefixWord ++ tailWord_2492973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492973).length < 2 ^ (prefixWord ++ tailWord_2492973).sum := by decide
  have hdescent : baseEnd_2492973 < baseStart_2492973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492981 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2492981 : Nat := 118140960795 + 2492981 * 2 ^ 59
def prefixEnd_2492981 : Nat := 4983230072969 + 3 ^ 40 * 2492981 * 2
def baseEnd_2492981 : Nat := 1280097515526415934072495

theorem tailTrace_2492981 : CollatzResearch.WordTrace tailWord_2492981 prefixEnd_2492981 1280097515526415934072495 := by
  unfold tailWord_2492981
  simp only [CollatzResearch.WordTrace]
  refine ⟨90926486981363079102846797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60617657987575386068564531 90926486981363079102846797)
  ·
    refine ⟨34097432618011154663567549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90926486981363079102846797 34097432618011154663567549)
    ·
      refine ⟨12786537231754182998837831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34097432618011154663567549 12786537231754182998837831)
      ·
        refine ⟨19179805847631274498256747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12786537231754182998837831 19179805847631274498256747)
        ·
          refine ⟨28769708771446911747385121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19179805847631274498256747 28769708771446911747385121)
          ·
            refine ⟨21577281578585183810538841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28769708771446911747385121 21577281578585183810538841)
            ·
              refine ⟨16182961183938887857904131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21577281578585183810538841 16182961183938887857904131)
              ·
                refine ⟨24274441775908331786856197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16182961183938887857904131 24274441775908331786856197)
                ·
                  refine ⟨4551457832982812210035537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24274441775908331786856197 4551457832982812210035537)
                  ·
                    refine ⟨3413593374737109157526653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551457832982812210035537 3413593374737109157526653)
                    ·
                      refine ⟨1280097515526415934072495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3413593374737109157526653 1280097515526415934072495)
                      ·
                        rfl

theorem cell23_2492981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2492981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492981 prefixEnd_2492981 := by exact prefixLift 2492981
  have htrace : WordTrace (prefixWord ++ tailWord_2492981) baseStart_2492981 baseEnd_2492981 := by
    simpa [prefixWord, tailWord_2492981, baseEnd_2492981] using wordTrace_append hprefix tailTrace_2492981
  have hstable : (prefixWord ++ tailWord_2492981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492981).length < 2 ^ (prefixWord ++ tailWord_2492981).sum := by decide
  have hdescent : baseEnd_2492981 < baseStart_2492981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492984 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 8]
def baseStart_2492984 : Nat := 118140960795 + 2492984 * 2 ^ 59
def prefixEnd_2492984 : Nat := 4983230072969 + 3 ^ 40 * 2492984 * 2
def baseEnd_2492984 : Nat := 142233228440931046926109

theorem tailTrace_2492984 : CollatzResearch.WordTrace tailWord_2492984 prefixEnd_2492984 142233228440931046926109 := by
  unfold tailWord_2492984
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463298200176105307603003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60617730933568140410137337 45463298200176105307603003)
  ·
    refine ⟨68194947300264157961404505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45463298200176105307603003 68194947300264157961404505)
    ·
      refine ⟨51146210475198118471053379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68194947300264157961404505 51146210475198118471053379)
      ·
        refine ⟨76719315712797177706580069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51146210475198118471053379 76719315712797177706580069)
        ·
          refine ⟨14384871696149470819983763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76719315712797177706580069 14384871696149470819983763)
          ·
            refine ⟨21577307544224206229975645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14384871696149470819983763 21577307544224206229975645)
            ·
              refine ⟨8091490329084077336240867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21577307544224206229975645 8091490329084077336240867)
              ·
                refine ⟨12137235493626116004361301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091490329084077336240867 12137235493626116004361301)
                ·
                  refine ⟨142233228440931046926109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12137235493626116004361301 142233228440931046926109)
                  ·
                    rfl

theorem cell23_2492984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_2492984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492984 prefixEnd_2492984 := by exact prefixLift 2492984
  have htrace : WordTrace (prefixWord ++ tailWord_2492984) baseStart_2492984 baseEnd_2492984 := by
    simpa [prefixWord, tailWord_2492984, baseEnd_2492984] using wordTrace_append hprefix tailTrace_2492984
  have hstable : (prefixWord ++ tailWord_2492984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492984).length < 2 ^ (prefixWord ++ tailWord_2492984).sum := by decide
  have hdescent : baseEnd_2492984 < baseStart_2492984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2492988 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_2492988 : Nat := 118140960795 + 2492988 * 2 ^ 59
def prefixEnd_2492988 : Nat := 4983230072969 + 3 ^ 40 * 2492988 * 2
def baseEnd_2492988 : Nat := 426700369963665802228321

theorem tailTrace_2492988 : CollatzResearch.WordTrace tailWord_2492988 prefixEnd_2492988 426700369963665802228321 := by
  unfold tailWord_2492988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463371146168859649175809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60617828194891812865567745 45463371146168859649175809)
  ·
    refine ⟨34097528359626644736881857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45463371146168859649175809 34097528359626644736881857)
    ·
      refine ⟨25573146269719983552661393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34097528359626644736881857 25573146269719983552661393)
      ·
        refine ⟨19179859702289987664496045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25573146269719983552661393 19179859702289987664496045)
        ·
          refine ⟨7192447388358745374186017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19179859702289987664496045 7192447388358745374186017)
          ·
            refine ⟨5394335541269059030639513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7192447388358745374186017 5394335541269059030639513)
            ·
              refine ⟨4045751655951794272979635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394335541269059030639513 4045751655951794272979635)
              ·
                refine ⟨6068627483927691409469453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045751655951794272979635 6068627483927691409469453)
                ·
                  refine ⟨2275735306472884278551045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6068627483927691409469453 2275735306472884278551045)
                  ·
                    refine ⟨426700369963665802228321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275735306472884278551045 426700369963665802228321)
                    ·
                      rfl

theorem cell23_2492988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_2492988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2492988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2492988 prefixEnd_2492988 := by exact prefixLift 2492988
  have htrace : WordTrace (prefixWord ++ tailWord_2492988) baseStart_2492988 baseEnd_2492988 := by
    simpa [prefixWord, tailWord_2492988, baseEnd_2492988] using wordTrace_append hprefix tailTrace_2492988
  have hstable : (prefixWord ++ tailWord_2492988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2492988).length < 2 ^ (prefixWord ++ tailWord_2492988).sum := by decide
  have hdescent : baseEnd_2492988 < baseStart_2492988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2492988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493004 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2493004 : Nat := 118140960795 + 2493004 * 2 ^ 59
def prefixEnd_2493004 : Nat := 4983230072969 + 3 ^ 40 * 2493004 * 2
def baseEnd_2493004 : Nat := 1280109325581469344084889

theorem tailTrace_2493004 : CollatzResearch.WordTrace tailWord_2493004 prefixEnd_2493004 1280109325581469344084889 := by
  unfold tailWord_2493004
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463662930139877015467033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60618217240186502687289377 45463662930139877015467033)
  ·
    refine ⟨34097747197604907761600275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45463662930139877015467033 34097747197604907761600275)
    ·
      refine ⟨51146620796407361642400413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34097747197604907761600275 51146620796407361642400413)
      ·
        refine ⟨19179982798652760615900155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51146620796407361642400413 19179982798652760615900155)
        ·
          refine ⟨28769974197979140923850233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19179982798652760615900155 28769974197979140923850233)
          ·
            refine ⟨21577480648484355692887675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28769974197979140923850233 21577480648484355692887675)
            ·
              refine ⟨32366220972726533539331513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21577480648484355692887675 32366220972726533539331513)
              ·
                refine ⟨24274665729544900154498635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32366220972726533539331513 24274665729544900154498635)
                ·
                  refine ⟨36411998594317350231747953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24274665729544900154498635 36411998594317350231747953)
                  ·
                    refine ⟨27308998945738012673810965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36411998594317350231747953 27308998945738012673810965)
                    ·
                      refine ⟨1280109325581469344084889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27308998945738012673810965 1280109325581469344084889)
                      ·
                        rfl

theorem cell23_2493004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2493004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493004 prefixEnd_2493004 := by exact prefixLift 2493004
  have htrace : WordTrace (prefixWord ++ tailWord_2493004) baseStart_2493004 baseEnd_2493004 := by
    simpa [prefixWord, tailWord_2493004, baseEnd_2493004] using wordTrace_append hprefix tailTrace_2493004
  have hstable : (prefixWord ++ tailWord_2493004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493004).length < 2 ^ (prefixWord ++ tailWord_2493004).sum := by decide
  have hdescent : baseEnd_2493004 < baseStart_2493004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493051 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 6, 2]
def baseStart_2493051 : Nat := 118140960795 + 2493051 * 2 ^ 59
def prefixEnd_2493051 : Nat := 4983230072969 + 3 ^ 40 * 2493051 * 2
def baseEnd_2493051 : Nat := 1280133459172230660197173

theorem tailTrace_2493051 : CollatzResearch.WordTrace tailWord_2493051 prefixEnd_2493051 1280133459172230660197173 := by
  unfold tailWord_2493051
  simp only [CollatzResearch.WordTrace]
  refine ⟨90929040091109481057895007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60619360060739654038596671 90929040091109481057895007)
  ·
    refine ⟨136393560136664221586842511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90929040091109481057895007 136393560136664221586842511)
    ·
      refine ⟨204590340204996332380263767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136393560136664221586842511 204590340204996332380263767)
      ·
        refine ⟨306885510307494498570395651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204590340204996332380263767 306885510307494498570395651)
        ·
          refine ⟨460328265461241747855593477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306885510307494498570395651 460328265461241747855593477)
          ·
            refine ⟨86311549773982827722923777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 460328265461241747855593477 86311549773982827722923777)
            ·
              refine ⟨64733662330487120792192833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86311549773982827722923777 64733662330487120792192833)
              ·
                refine ⟨48550246747865340594144625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64733662330487120792192833 48550246747865340594144625)
                ·
                  refine ⟨36412685060899005445608469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48550246747865340594144625 36412685060899005445608469)
                  ·
                    refine ⟨1706844612229640880262897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36412685060899005445608469 1706844612229640880262897)
                    ·
                      refine ⟨1280133459172230660197173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706844612229640880262897 1280133459172230660197173)
                      ·
                        rfl

theorem cell23_2493051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6, 2].length) (baseStart_2493051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493051 prefixEnd_2493051 := by exact prefixLift 2493051
  have htrace : WordTrace (prefixWord ++ tailWord_2493051) baseStart_2493051 baseEnd_2493051 := by
    simpa [prefixWord, tailWord_2493051, baseEnd_2493051] using wordTrace_append hprefix tailTrace_2493051
  have hstable : (prefixWord ++ tailWord_2493051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493051).length < 2 ^ (prefixWord ++ tailWord_2493051).sum := by decide
  have hdescent : baseEnd_2493051 < baseStart_2493051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_2493071 : Nat := 118140960795 + 2493071 * 2 ^ 59
def prefixEnd_2493071 : Nat := 4983230072969 + 3 ^ 40 * 2493071 * 2
def baseEnd_2493071 : Nat := 1280143728785320581947081

theorem tailTrace_2493071 : CollatzResearch.WordTrace tailWord_2493071 prefixEnd_2493071 1280143728785320581947081 := by
  unfold tailWord_2493071
  simp only [CollatzResearch.WordTrace]
  refine ⟨90929769551037024473623067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60619846367358016315748711 90929769551037024473623067)
  ·
    refine ⟨136394654326555536710434601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90929769551037024473623067 136394654326555536710434601)
    ·
      refine ⟨102295990744916652532825951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136394654326555536710434601 102295990744916652532825951)
      ·
        refine ⟨153443986117374978799238927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102295990744916652532825951 153443986117374978799238927)
        ·
          refine ⟨230165979176062468198858391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153443986117374978799238927 230165979176062468198858391)
          ·
            refine ⟨345248968764093702298287587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230165979176062468198858391 345248968764093702298287587)
            ·
              refine ⟨517873453146140553447431381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345248968764093702298287587 517873453146140553447431381)
              ·
                refine ⟨12137659058112669221424173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 517873453146140553447431381 12137659058112669221424173)
                ·
                  refine ⟨4551622146792250958034065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12137659058112669221424173 4551622146792250958034065)
                  ·
                    refine ⟨3413716610094188218525549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551622146792250958034065 3413716610094188218525549)
                    ·
                      refine ⟨1280143728785320581947081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3413716610094188218525549 1280143728785320581947081)
                      ·
                        rfl

theorem cell23_2493071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_2493071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493071 prefixEnd_2493071 := by exact prefixLift 2493071
  have htrace : WordTrace (prefixWord ++ tailWord_2493071) baseStart_2493071 baseEnd_2493071 := by
    simpa [prefixWord, tailWord_2493071, baseEnd_2493071] using wordTrace_append hprefix tailTrace_2493071
  have hstable : (prefixWord ++ tailWord_2493071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493071).length < 2 ^ (prefixWord ++ tailWord_2493071).sum := by decide
  have hdescent : baseEnd_2493071 < baseStart_2493071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493081 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_2493081 : Nat := 118140960795 + 2493081 * 2 ^ 59
def prefixEnd_2493081 : Nat := 4983230072969 + 3 ^ 40 * 2493081 * 2
def baseEnd_2493081 : Nat := 1280148863591865542822035

theorem tailTrace_2493081 : CollatzResearch.WordTrace tailWord_2493081 prefixEnd_2493081 1280148863591865542822035 := by
  unfold tailWord_2493081
  simp only [CollatzResearch.WordTrace]
  refine ⟨90930134281000796181487097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60620089520667197454324731 90930134281000796181487097)
  ·
    refine ⟨68197600710750597136115323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90930134281000796181487097 68197600710750597136115323)
    ·
      refine ⟨102296401066125895704172985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68197600710750597136115323 102296401066125895704172985)
      ·
        refine ⟨76722300799594421778129739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102296401066125895704172985 76722300799594421778129739)
        ·
          refine ⟨115083451199391632667194609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76722300799594421778129739 115083451199391632667194609)
          ·
            refine ⟨86312588399543724500395957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115083451199391632667194609 86312588399543724500395957)
            ·
              refine ⟨8091805162457224171912121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86312588399543724500395957 8091805162457224171912121)
              ·
                refine ⟨6068853871842918128934091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8091805162457224171912121 6068853871842918128934091)
                ·
                  refine ⟨9103280807764377193401137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068853871842918128934091 9103280807764377193401137)
                  ·
                    refine ⟨6827460605823282895050853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9103280807764377193401137 6827460605823282895050853)
                    ·
                      refine ⟨1280148863591865542822035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6827460605823282895050853 1280148863591865542822035)
                      ·
                        rfl

theorem cell23_2493081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_2493081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493081 prefixEnd_2493081 := by exact prefixLift 2493081
  have htrace : WordTrace (prefixWord ++ tailWord_2493081) baseStart_2493081 baseEnd_2493081 := by
    simpa [prefixWord, tailWord_2493081, baseEnd_2493081] using wordTrace_append hprefix tailTrace_2493081
  have hstable : (prefixWord ++ tailWord_2493081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493081).length < 2 ^ (prefixWord ++ tailWord_2493081).sum := by decide
  have hdescent : baseEnd_2493081 < baseStart_2493081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493082 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_2493082 : Nat := 118140960795 + 2493082 * 2 ^ 59
def prefixEnd_2493082 : Nat := 4983230072969 + 3 ^ 40 * 2493082 * 2
def baseEnd_2493082 : Nat := 426716459024173346303177

theorem tailTrace_2493082 : CollatzResearch.WordTrace tailWord_2493082 prefixEnd_2493082 426716459024173346303177 := by
  unfold tailWord_2493082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22732542688499293338068375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60620113835998115568182333 22732542688499293338068375)
  ·
    refine ⟨34098814032748940007102563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22732542688499293338068375 34098814032748940007102563)
    ·
      refine ⟨51148221049123410010653845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34098814032748940007102563 51148221049123410010653845)
      ·
        refine ⟨2397572861677659844249399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51148221049123410010653845 2397572861677659844249399)
        ·
          refine ⟨3596359292516489766374099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397572861677659844249399 3596359292516489766374099)
          ·
            refine ⟨5394538938774734649561149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596359292516489766374099 5394538938774734649561149)
            ·
              refine ⟨2022952102040525493585431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5394538938774734649561149 2022952102040525493585431)
              ·
                refine ⟨3034428153060788240378147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022952102040525493585431 3034428153060788240378147)
                ·
                  refine ⟨4551642229591182360567221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034428153060788240378147 4551642229591182360567221)
                  ·
                    refine ⟨426716459024173346303177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4551642229591182360567221 426716459024173346303177)
                    ·
                      rfl

theorem cell23_2493082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_2493082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493082 prefixEnd_2493082 := by exact prefixLift 2493082
  have htrace : WordTrace (prefixWord ++ tailWord_2493082) baseStart_2493082 baseEnd_2493082 := by
    simpa [prefixWord, tailWord_2493082, baseEnd_2493082] using wordTrace_append hprefix tailTrace_2493082
  have hstable : (prefixWord ++ tailWord_2493082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493082).length < 2 ^ (prefixWord ++ tailWord_2493082).sum := by decide
  have hdescent : baseEnd_2493082 < baseStart_2493082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493145 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 1, 3, 2]
def baseStart_2493145 : Nat := 118140960795 + 2493145 * 2 ^ 59
def prefixEnd_2493145 : Nat := 4983230072969 + 3 ^ 40 * 2493145 * 2
def baseEnd_2493145 : Nat := 1280181726353753292421741

theorem tailTrace_2493145 : CollatzResearch.WordTrace tailWord_2493145 prefixEnd_2493145 1280181726353753292421741 := by
  unfold tailWord_2493145
  simp only [CollatzResearch.WordTrace]
  refine ⟨90932468552768935111816889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60621645701845956741211259 90932468552768935111816889)
  ·
    refine ⟨68199351414576701333862667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90932468552768935111816889 68199351414576701333862667)
    ·
      refine ⟨102299027121865052000794001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68199351414576701333862667 102299027121865052000794001)
      ·
        refine ⟨76724270341398789000595501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102299027121865052000794001 76724270341398789000595501)
        ·
          refine ⟨28771601378024545875223313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76724270341398789000595501 28771601378024545875223313)
          ·
            refine ⟨21578701033518409406417485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28771601378024545875223313 21578701033518409406417485)
            ·
              refine ⟨8092012887569403527406557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21578701033518409406417485 8092012887569403527406557)
              ·
                refine ⟨3034504832838526322777459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8092012887569403527406557 3034504832838526322777459)
                ·
                  refine ⟨4551757249257789484166189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034504832838526322777459 4551757249257789484166189)
                  ·
                    refine ⟨1706908968471671056562321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4551757249257789484166189 1706908968471671056562321)
                    ·
                      refine ⟨1280181726353753292421741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706908968471671056562321 1280181726353753292421741)
                      ·
                        rfl

theorem cell23_2493145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_2493145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493145 prefixEnd_2493145 := by exact prefixLift 2493145
  have htrace : WordTrace (prefixWord ++ tailWord_2493145) baseStart_2493145 baseEnd_2493145 := by
    simpa [prefixWord, tailWord_2493145, baseEnd_2493145] using wordTrace_append hprefix tailTrace_2493145
  have hstable : (prefixWord ++ tailWord_2493145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493145).length < 2 ^ (prefixWord ++ tailWord_2493145).sum := by decide
  have hdescent : baseEnd_2493145 < baseStart_2493145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493151 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 2, 6]
def baseStart_2493151 : Nat := 118140960795 + 2493151 * 2 ^ 59
def prefixEnd_2493151 : Nat := 4983230072969 + 3 ^ 40 * 2493151 * 2
def baseEnd_2493151 : Nat := 426728269079226756315571

theorem tailTrace_2493151 : CollatzResearch.WordTrace tailWord_2493151 prefixEnd_2493151 426728269079226756315571 := by
  unfold tailWord_2493151
  simp only [CollatzResearch.WordTrace]
  refine ⟨90932687390747198136535307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60621791593831465424356871 90932687390747198136535307)
  ·
    refine ⟨136399031086120797204802961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90932687390747198136535307 136399031086120797204802961)
    ·
      refine ⟨102299273314590597903602221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136399031086120797204802961 102299273314590597903602221)
      ·
        refine ⟨38362227492971474213850833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102299273314590597903602221 38362227492971474213850833)
        ·
          refine ⟨28771670619728605660388125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38362227492971474213850833 28771670619728605660388125)
          ·
            refine ⟨10789376482398227122645547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28771670619728605660388125 10789376482398227122645547)
            ·
              refine ⟨16184064723597340683968321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10789376482398227122645547 16184064723597340683968321)
              ·
                refine ⟨12138048542698005512976241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16184064723597340683968321 12138048542698005512976241)
                ·
                  refine ⟨9103536407023504134732181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12138048542698005512976241 9103536407023504134732181)
                  ·
                    refine ⟨426728269079226756315571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9103536407023504134732181 426728269079226756315571)
                    ·
                      rfl

theorem cell23_2493151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_2493151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493151 prefixEnd_2493151 := by exact prefixLift 2493151
  have htrace : WordTrace (prefixWord ++ tailWord_2493151) baseStart_2493151 baseEnd_2493151 := by
    simpa [prefixWord, tailWord_2493151, baseEnd_2493151] using wordTrace_append hprefix tailTrace_2493151
  have hstable : (prefixWord ++ tailWord_2493151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493151).length < 2 ^ (prefixWord ++ tailWord_2493151).sum := by decide
  have hdescent : baseEnd_2493151 < baseStart_2493151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493161 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_2493161 : Nat := 118140960795 + 2493161 * 2 ^ 59
def prefixEnd_2493161 : Nat := 4983230072969 + 3 ^ 40 * 2493161 * 2
def baseEnd_2493161 : Nat := 1280189942044225229821667

theorem tailTrace_2493161 : CollatzResearch.WordTrace tailWord_2493161 prefixEnd_2493161 1280189942044225229821667 := by
  unfold tailWord_2493161
  simp only [CollatzResearch.WordTrace]
  refine ⟨90933052120710969844399337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60622034747140646562932891 90933052120710969844399337)
  ·
    refine ⟨68199789090533227383299503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90933052120710969844399337 68199789090533227383299503)
    ·
      refine ⟨102299683635799841074949255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68199789090533227383299503 102299683635799841074949255)
      ·
        refine ⟨153449525453699761612423883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102299683635799841074949255 153449525453699761612423883)
        ·
          refine ⟨230174288180549642418635825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153449525453699761612423883 230174288180549642418635825)
          ·
            refine ⟨172630716135412231813976869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230174288180549642418635825 172630716135412231813976869)
            ·
              refine ⟨32368259275389793465120663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172630716135412231813976869 32368259275389793465120663)
              ·
                refine ⟨48552388913084690197680995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32368259275389793465120663 48552388913084690197680995)
                ·
                  refine ⟨72828583369627035296521493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48552388913084690197680995 72828583369627035296521493)
                  ·
                    refine ⟨3413839845451267279524445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72828583369627035296521493 3413839845451267279524445)
                    ·
                      refine ⟨1280189942044225229821667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3413839845451267279524445 1280189942044225229821667)
                      ·
                        rfl

theorem cell23_2493161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_2493161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493161 prefixEnd_2493161 := by exact prefixLift 2493161
  have htrace : WordTrace (prefixWord ++ tailWord_2493161) baseStart_2493161 baseEnd_2493161 := by
    simpa [prefixWord, tailWord_2493161, baseEnd_2493161] using wordTrace_append hprefix tailTrace_2493161
  have hstable : (prefixWord ++ tailWord_2493161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493161).length < 2 ^ (prefixWord ++ tailWord_2493161).sum := by decide
  have hdescent : baseEnd_2493161 < baseStart_2493161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493181 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 7]
def baseStart_2493181 : Nat := 118140960795 + 2493181 * 2 ^ 59
def prefixEnd_2493181 : Nat := 4983230072969 + 3 ^ 40 * 2493181 * 2
def baseEnd_2493181 : Nat := 142244467961923905730175

theorem tailTrace_2493181 : CollatzResearch.WordTrace tailWord_2493181 prefixEnd_2493181 142244467961923905730175 := by
  unfold tailWord_2493181
  simp only [CollatzResearch.WordTrace]
  refine ⟨90933781580638513260127397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60622521053759008840084931 90933781580638513260127397)
  ·
    refine ⟨17050084046369721236273887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90933781580638513260127397 17050084046369721236273887)
    ·
      refine ⟨25575126069554581854410831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17050084046369721236273887 25575126069554581854410831)
      ·
        refine ⟨38362689104331872781616247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25575126069554581854410831 38362689104331872781616247)
        ·
          refine ⟨57544033656497809172424371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38362689104331872781616247 57544033656497809172424371)
          ·
            refine ⟨86316050484746713758636557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57544033656497809172424371 86316050484746713758636557)
            ·
              refine ⟨32368518931780017659488709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86316050484746713758636557 32368518931780017659488709)
              ·
                refine ⟨6069097299708753311154133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32368518931780017659488709 6069097299708753311154133)
                ·
                  refine ⟨142244467961923905730175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6069097299708753311154133 142244467961923905730175)
                  ·
                    rfl

theorem cell23_2493181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_2493181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493181 prefixEnd_2493181 := by exact prefixLift 2493181
  have htrace : WordTrace (prefixWord ++ tailWord_2493181) baseStart_2493181 baseEnd_2493181 := by
    simpa [prefixWord, tailWord_2493181, baseEnd_2493181] using wordTrace_append hprefix tailTrace_2493181
  have hstable : (prefixWord ++ tailWord_2493181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493181).length < 2 ^ (prefixWord ++ tailWord_2493181).sum := by decide
  have hdescent : baseEnd_2493181 < baseStart_2493181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493226 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2493226 : Nat := 118140960795 + 2493226 * 2 ^ 59
def prefixEnd_2493226 : Nat := 4983230072969 + 3 ^ 40 * 2493226 * 2
def baseEnd_2493226 : Nat := 1280223318286767475508869

theorem tailTrace_2493226 : CollatzResearch.WordTrace tailWord_2493226 prefixEnd_2493226 1280223318286767475508869 := by
  unfold tailWord_2493226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22733855716368871486378883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60623615243650323963677021 22733855716368871486378883)
  ·
    refine ⟨34100783574553307229568325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22733855716368871486378883 34100783574553307229568325)
    ·
      refine ⟨6393896920228745105544061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34100783574553307229568325 6393896920228745105544061)
      ·
        refine ⟨2397711345085779414579023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6393896920228745105544061 2397711345085779414579023)
        ·
          refine ⟨3596567017628669121868535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397711345085779414579023 3596567017628669121868535)
          ·
            refine ⟨5394850526443003682802803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596567017628669121868535 5394850526443003682802803)
            ·
              refine ⟨8092275789664505524204205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394850526443003682802803 8092275789664505524204205)
              ·
                refine ⟨3034603421124189571576577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8092275789664505524204205 3034603421124189571576577)
                ·
                  refine ⟨2275952565843142178682433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034603421124189571576577 2275952565843142178682433)
                  ·
                    refine ⟨1706964424382356634011825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2275952565843142178682433 1706964424382356634011825)
                    ·
                      refine ⟨1280223318286767475508869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1706964424382356634011825 1280223318286767475508869)
                      ·
                        rfl

theorem cell23_2493226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2493226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493226 prefixEnd_2493226 := by exact prefixLift 2493226
  have htrace : WordTrace (prefixWord ++ tailWord_2493226) baseStart_2493226 baseEnd_2493226 := by
    simpa [prefixWord, tailWord_2493226, baseEnd_2493226] using wordTrace_append hprefix tailTrace_2493226
  have hstable : (prefixWord ++ tailWord_2493226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493226).length < 2 ^ (prefixWord ++ tailWord_2493226).sum := by decide
  have hdescent : baseEnd_2493226 < baseStart_2493226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493258 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_2493258 : Nat := 118140960795 + 2493258 * 2 ^ 59
def prefixEnd_2493258 : Nat := 4983230072969 + 3 ^ 40 * 2493258 * 2
def baseEnd_2493258 : Nat := 426746583222570450102907

theorem tailTrace_2493258 : CollatzResearch.WordTrace tailWord_2493258 prefixEnd_2493258 426746583222570450102907 := by
  unfold tailWord_2493258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22734147500339888852670107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60624393334239703607120285 22734147500339888852670107)
  ·
    refine ⟨34101221250509833279005161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22734147500339888852670107 34101221250509833279005161)
    ·
      refine ⟨25575915937882374959253871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34101221250509833279005161 25575915937882374959253871)
      ·
        refine ⟨38363873906823562438880807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25575915937882374959253871 38363873906823562438880807)
        ·
          refine ⟨57545810860235343658321211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38363873906823562438880807 57545810860235343658321211)
          ·
            refine ⟨86318716290353015487481817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57545810860235343658321211 86318716290353015487481817)
            ·
              refine ⟨64739037217764761615611363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86318716290353015487481817 64739037217764761615611363)
              ·
                refine ⟨97108555826647142423417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64739037217764761615611363 97108555826647142423417045)
                ·
                  refine ⟨2275981777187042400548837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 97108555826647142423417045 2275981777187042400548837)
                  ·
                    refine ⟨426746583222570450102907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275981777187042400548837 426746583222570450102907)
                    ·
                      rfl

theorem cell23_2493258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_2493258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493258 prefixEnd_2493258 := by exact prefixLift 2493258
  have htrace : WordTrace (prefixWord ++ tailWord_2493258) baseStart_2493258 baseEnd_2493258 := by
    simpa [prefixWord, tailWord_2493258, baseEnd_2493258] using wordTrace_append hprefix tailTrace_2493258
  have hstable : (prefixWord ++ tailWord_2493258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493258).length < 2 ^ (prefixWord ++ tailWord_2493258).sum := by decide
  have hdescent : baseEnd_2493258 < baseStart_2493258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493302 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2493302 : Nat := 118140960795 + 2493302 * 2 ^ 59
def prefixEnd_2493302 : Nat := 4983230072969 + 3 ^ 40 * 2493302 * 2
def baseEnd_2493302 : Nat := 1280262342816509178158519

theorem tailTrace_2493302 : CollatzResearch.WordTrace tailWord_2493302 prefixEnd_2493302 1280262342816509178158519 := by
  unfold tailWord_2493302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5683637175825009432830135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60625463208800100616854773 5683637175825009432830135)
  ·
    refine ⟨8525455763737514149245203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5683637175825009432830135 8525455763737514149245203)
    ·
      refine ⟨12788183645606271223867805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525455763737514149245203 12788183645606271223867805)
      ·
        refine ⟨4795568867102351708950427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12788183645606271223867805 4795568867102351708950427)
        ·
          refine ⟨7193353300653527563425641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795568867102351708950427 7193353300653527563425641)
          ·
            refine ⟨5395014975490145672569231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7193353300653527563425641 5395014975490145672569231)
            ·
              refine ⟨8092522463235218508853847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395014975490145672569231 8092522463235218508853847)
              ·
                refine ⟨12138783694852827763280771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8092522463235218508853847 12138783694852827763280771)
                ·
                  refine ⟨18208175542279241644921157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12138783694852827763280771 18208175542279241644921157)
                  ·
                    refine ⟨3414032914177357808422717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18208175542279241644921157 3414032914177357808422717)
                    ·
                      refine ⟨1280262342816509178158519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3414032914177357808422717 1280262342816509178158519)
                      ·
                        rfl

theorem cell23_2493302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2493302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493302 prefixEnd_2493302 := by exact prefixLift 2493302
  have htrace : WordTrace (prefixWord ++ tailWord_2493302) baseStart_2493302 baseEnd_2493302 := by
    simpa [prefixWord, tailWord_2493302, baseEnd_2493302] using wordTrace_append hprefix tailTrace_2493302
  have hstable : (prefixWord ++ tailWord_2493302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493302).length < 2 ^ (prefixWord ++ tailWord_2493302).sum := by decide
  have hdescent : baseEnd_2493302 < baseStart_2493302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493315 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 3]
def baseStart_2493315 : Nat := 118140960795 + 2493315 * 2 ^ 59
def prefixEnd_2493315 : Nat := 4983230072969 + 3 ^ 40 * 2493315 * 2
def baseEnd_2493315 : Nat := 1280269018065017627295959

theorem tailTrace_2493315 : CollatzResearch.WordTrace tailWord_2493315 prefixEnd_2493315 1280269018065017627295959 := by
  unfold tailWord_2493315
  simp only [CollatzResearch.WordTrace]
  refine ⟨90938668962153054145505399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60625779308102036097003599 90938668962153054145505399)
  ·
    refine ⟨136408003443229581218258099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90938668962153054145505399 136408003443229581218258099)
    ·
      refine ⟨204612005164844371827387149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136408003443229581218258099 204612005164844371827387149)
      ·
        refine ⟨76729501936816639435270181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204612005164844371827387149 76729501936816639435270181)
        ·
          refine ⟨14386781613153119894113159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76729501936816639435270181 14386781613153119894113159)
          ·
            refine ⟨21580172419729679841169739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14386781613153119894113159 21580172419729679841169739)
            ·
              refine ⟨32370258629594519761754609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21580172419729679841169739 32370258629594519761754609)
              ·
                refine ⟨24277693972195889821315957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32370258629594519761754609 24277693972195889821315957)
                ·
                  refine ⟨2276033809893364670748371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24277693972195889821315957 2276033809893364670748371)
                  ·
                    refine ⟨3414050714840047006122557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2276033809893364670748371 3414050714840047006122557)
                    ·
                      refine ⟨1280269018065017627295959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3414050714840047006122557 1280269018065017627295959)
                      ·
                        rfl

theorem cell23_2493315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_2493315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493315 prefixEnd_2493315 := by exact prefixLift 2493315
  have htrace : WordTrace (prefixWord ++ tailWord_2493315) baseStart_2493315 baseEnd_2493315 := by
    simpa [prefixWord, tailWord_2493315, baseEnd_2493315] using wordTrace_append hprefix tailTrace_2493315
  have hstable : (prefixWord ++ tailWord_2493315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493315).length < 2 ^ (prefixWord ++ tailWord_2493315).sum := by decide
  have hdescent : baseEnd_2493315 < baseStart_2493315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493322 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_2493322 : Nat := 118140960795 + 2493322 * 2 ^ 59
def prefixEnd_2493322 : Nat := 4983230072969 + 3 ^ 40 * 2493322 * 2
def baseEnd_2493322 : Nat := 142252512492177677767603

theorem tailTrace_2493322 : CollatzResearch.WordTrace tailWord_2493322 prefixEnd_2493322 142252512492177677767603 := by
  unfold tailWord_2493322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22734731068281923585252555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60625949515418462894006813 22734731068281923585252555)
  ·
    refine ⟨34102096602422885377878833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22734731068281923585252555 34102096602422885377878833)
    ·
      refine ⟨25576572451817164033409125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34102096602422885377878833 25576572451817164033409125)
      ·
        refine ⟨4795607334715718256264211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25576572451817164033409125 4795607334715718256264211)
        ·
          refine ⟨7193411002073577384396317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795607334715718256264211 7193411002073577384396317)
          ·
            refine ⟨2697529125777591519148619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7193411002073577384396317 2697529125777591519148619)
            ·
              refine ⟨4046293688666387278722929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697529125777591519148619 4046293688666387278722929)
              ·
                refine ⟨3034720266499790459042197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046293688666387278722929 3034720266499790459042197)
                ·
                  refine ⟨142252512492177677767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3034720266499790459042197 142252512492177677767603)
                  ·
                    rfl

theorem cell23_2493322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_2493322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493322 prefixEnd_2493322 := by exact prefixLift 2493322
  have htrace : WordTrace (prefixWord ++ tailWord_2493322) baseStart_2493322 baseEnd_2493322 := by
    simpa [prefixWord, tailWord_2493322, baseEnd_2493322] using wordTrace_append hprefix tailTrace_2493322
  have hstable : (prefixWord ++ tailWord_2493322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493322).length < 2 ^ (prefixWord ++ tailWord_2493322).sum := by decide
  have hdescent : baseEnd_2493322 < baseStart_2493322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493365 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2493365 : Nat := 118140960795 + 2493365 * 2 ^ 59
def prefixEnd_2493365 : Nat := 4983230072969 + 3 ^ 40 * 2493365 * 2
def baseEnd_2493365 : Nat := 426764897365914143890243

theorem tailTrace_2493365 : CollatzResearch.WordTrace tailWord_2493365 prefixEnd_2493365 426764897365914143890243 := by
  unfold tailWord_2493365
  simp only [CollatzResearch.WordTrace]
  refine ⟨90940492611971912684825549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60626995074647941789883699 90940492611971912684825549)
  ·
    refine ⟨34102684729489467256809581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90940492611971912684825549 34102684729489467256809581)
    ·
      refine ⟨12788506773558550221303593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34102684729489467256809581 12788506773558550221303593)
      ·
        refine ⟨9591380080168912665977695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12788506773558550221303593 9591380080168912665977695)
        ·
          refine ⟨14387070120253368998966543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9591380080168912665977695 14387070120253368998966543)
          ·
            refine ⟨21580605180380053498449815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14387070120253368998966543 21580605180380053498449815)
            ·
              refine ⟨32370907770570080247674723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21580605180380053498449815 32370907770570080247674723)
              ·
                refine ⟨48556361655855120371512085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32370907770570080247674723 48556361655855120371512085)
                ·
                  refine ⟨2276079452618208767414629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48556361655855120371512085 2276079452618208767414629)
                  ·
                    refine ⟨426764897365914143890243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2276079452618208767414629 426764897365914143890243)
                    ·
                      rfl

theorem cell23_2493365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2493365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493365 prefixEnd_2493365 := by exact prefixLift 2493365
  have htrace : WordTrace (prefixWord ++ tailWord_2493365) baseStart_2493365 baseEnd_2493365 := by
    simpa [prefixWord, tailWord_2493365, baseEnd_2493365] using wordTrace_append hprefix tailTrace_2493365
  have hstable : (prefixWord ++ tailWord_2493365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493365).length < 2 ^ (prefixWord ++ tailWord_2493365).sum := by decide
  have hdescent : baseEnd_2493365 < baseStart_2493365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493426 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2493426 : Nat := 118140960795 + 2493426 * 2 ^ 59
def prefixEnd_2493426 : Nat := 4983230072969 + 3 ^ 40 * 2493426 * 2
def baseEnd_2493426 : Nat := 1280326014417666693007949

theorem tailTrace_2493426 : CollatzResearch.WordTrace tailWord_2493426 prefixEnd_2493426 1280326014417666693007949 := by
  unfold tailWord_2493426
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735679366187730025699033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60628478309833946735197421 22735679366187730025699033)
  ·
    refine ⟨17051759524640797519274275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22735679366187730025699033 17051759524640797519274275)
    ·
      refine ⟨25577639286961196278911413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17051759524640797519274275 25577639286961196278911413)
      ·
        refine ⟨2397903683152612151147945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25577639286961196278911413 2397903683152612151147945)
        ·
          refine ⟨1798427762364459113360959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397903683152612151147945 1798427762364459113360959)
          ·
            refine ⟨2697641643546688670041439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798427762364459113360959 2697641643546688670041439)
            ·
              refine ⟨4046462465320033005062159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697641643546688670041439 4046462465320033005062159)
              ·
                refine ⟨6069693697980049507593239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4046462465320033005062159 6069693697980049507593239)
                ·
                  refine ⟨9104540546970074261389859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6069693697980049507593239 9104540546970074261389859)
                  ·
                    refine ⟨13656810820455111392084789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9104540546970074261389859 13656810820455111392084789)
                    ·
                      refine ⟨1280326014417666693007949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13656810820455111392084789 1280326014417666693007949)
                      ·
                        rfl

theorem cell23_2493426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2493426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493426 prefixEnd_2493426 := by exact prefixLift 2493426
  have htrace : WordTrace (prefixWord ++ tailWord_2493426) baseStart_2493426 baseEnd_2493426 := by
    simpa [prefixWord, tailWord_2493426, baseEnd_2493426] using wordTrace_append hprefix tailTrace_2493426
  have hstable : (prefixWord ++ tailWord_2493426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493426).length < 2 ^ (prefixWord ++ tailWord_2493426).sum := by decide
  have hdescent : baseEnd_2493426 < baseStart_2493426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493496 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_2493496 : Nat := 118140960795 + 2493496 * 2 ^ 59
def prefixEnd_2493496 : Nat := 4983230072969 + 3 ^ 40 * 2493496 * 2
def baseEnd_2493496 : Nat := 1280361958063481419132627

theorem tailTrace_2493496 : CollatzResearch.WordTrace tailWord_2493496 prefixEnd_2493496 1280361958063481419132627 := by
  unfold tailWord_2493496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45472635287248661028922171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60630180382998214705229561 45472635287248661028922171)
  ·
    refine ⟨68208952930872991543383257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45472635287248661028922171 68208952930872991543383257)
    ·
      refine ⟨51156714698154743657537443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68208952930872991543383257 51156714698154743657537443)
      ·
        refine ⟨76735072047232115486306165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51156714698154743657537443 76735072047232115486306165)
        ·
          refine ⟨7193913004428010826841203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76735072047232115486306165 7193913004428010826841203)
          ·
            refine ⟨10790869506642016240261805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7193913004428010826841203 10790869506642016240261805)
            ·
              refine ⟨4046576064990756090098177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10790869506642016240261805 4046576064990756090098177)
              ·
                refine ⟨3034932048743067067573633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046576064990756090098177 3034932048743067067573633)
                ·
                  refine ⟨2276199036557300300680225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3034932048743067067573633 2276199036557300300680225)
                  ·
                    refine ⟨1707149277417975225510169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276199036557300300680225 1707149277417975225510169)
                    ·
                      refine ⟨1280361958063481419132627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707149277417975225510169 1280361958063481419132627)
                      ·
                        rfl

theorem cell23_2493496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_2493496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493496 prefixEnd_2493496 := by exact prefixLift 2493496
  have htrace : WordTrace (prefixWord ++ tailWord_2493496) baseStart_2493496 baseEnd_2493496 := by
    simpa [prefixWord, tailWord_2493496, baseEnd_2493496] using wordTrace_append hprefix tailTrace_2493496
  have hstable : (prefixWord ++ tailWord_2493496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493496).length < 2 ^ (prefixWord ++ tailWord_2493496).sum := by decide
  have hdescent : baseEnd_2493496 < baseStart_2493496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493502 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2493502 : Nat := 118140960795 + 2493502 * 2 ^ 59
def prefixEnd_2493502 : Nat := 4983230072969 + 3 ^ 40 * 2493502 * 2
def baseEnd_2493502 : Nat := 142262782105267599517511

theorem tailTrace_2493502 : CollatzResearch.WordTrace tailWord_2493502 prefixEnd_2493502 142262782105267599517511 := by
  unfold tailWord_2493502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368186176559448135320345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60630326274983723388375173 11368186176559448135320345)
  ·
    refine ⟨8526139632419586101490259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11368186176559448135320345 8526139632419586101490259)
    ·
      refine ⟨12789209448629379152235389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8526139632419586101490259 12789209448629379152235389)
      ·
        refine ⟨4795953543236017182088271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12789209448629379152235389 4795953543236017182088271)
        ·
          refine ⟨7193930314854025773132407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795953543236017182088271 7193930314854025773132407)
          ·
            refine ⟨10790895472281038659698611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7193930314854025773132407 10790895472281038659698611)
            ·
              refine ⟨16186343208421557989547917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10790895472281038659698611 16186343208421557989547917)
              ·
                refine ⟨6069878703158084246080469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16186343208421557989547917 6069878703158084246080469)
                ·
                  refine ⟨142262782105267599517511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6069878703158084246080469 142262782105267599517511)
                  ·
                    rfl

theorem cell23_2493502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2493502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493502 prefixEnd_2493502 := by exact prefixLift 2493502
  have htrace : WordTrace (prefixWord ++ tailWord_2493502) baseStart_2493502 baseEnd_2493502 := by
    simpa [prefixWord, tailWord_2493502, baseEnd_2493502] using wordTrace_append hprefix tailTrace_2493502
  have hstable : (prefixWord ++ tailWord_2493502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493502).length < 2 ^ (prefixWord ++ tailWord_2493502).sum := by decide
  have hdescent : baseEnd_2493502 < baseStart_2493502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493532 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2493532 : Nat := 118140960795 + 2493532 * 2 ^ 59
def prefixEnd_2493532 : Nat := 4983230072969 + 3 ^ 40 * 2493532 * 2
def baseEnd_2493532 : Nat := 426793481122347759427487

theorem tailTrace_2493532 : CollatzResearch.WordTrace tailWord_2493532 prefixEnd_2493532 426793481122347759427487 := by
  unfold tailWord_2493532
  simp only [CollatzResearch.WordTrace]
  refine ⟨45473291801183450103077425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60631055734911266804103233 45473291801183450103077425)
  ·
    refine ⟨34104968850887587577308069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45473291801183450103077425 34104968850887587577308069)
    ·
      refine ⟨6394681659541422670745263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34104968850887587577308069 6394681659541422670745263)
      ·
        refine ⟨9592022489312134006117895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394681659541422670745263 9592022489312134006117895)
        ·
          refine ⟨14388033733968201009176843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9592022489312134006117895 14388033733968201009176843)
          ·
            refine ⟨21582050600952301513765265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14388033733968201009176843 21582050600952301513765265)
            ·
              refine ⟨16186537950714226135323949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21582050600952301513765265 16186537950714226135323949)
              ·
                refine ⟨6069951731517834800746481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16186537950714226135323949 6069951731517834800746481)
                ·
                  refine ⟨4552463798638376100559861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6069951731517834800746481 4552463798638376100559861)
                  ·
                    refine ⟨426793481122347759427487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4552463798638376100559861 426793481122347759427487)
                    ·
                      rfl

theorem cell23_2493532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2493532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493532 prefixEnd_2493532 := by exact prefixLift 2493532
  have htrace : WordTrace (prefixWord ++ tailWord_2493532) baseStart_2493532 baseEnd_2493532 := by
    simpa [prefixWord, tailWord_2493532, baseEnd_2493532] using wordTrace_append hprefix tailTrace_2493532
  have hstable : (prefixWord ++ tailWord_2493532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493532).length < 2 ^ (prefixWord ++ tailWord_2493532).sum := by decide
  have hdescent : baseEnd_2493532 < baseStart_2493532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493535 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2493535 : Nat := 118140960795 + 2493535 * 2 ^ 59
def prefixEnd_2493535 : Nat := 4983230072969 + 3 ^ 40 * 2493535 * 2
def baseEnd_2493535 : Nat := 1280381983809006766544947

theorem tailTrace_2493535 : CollatzResearch.WordTrace tailWord_2493535 prefixEnd_2493535 1280381983809006766544947 := by
  unfold tailWord_2493535
  simp only [CollatzResearch.WordTrace]
  refine ⟨90946693021356031718514059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60631128680904021145676039 90946693021356031718514059)
  ·
    refine ⟨136420039532034047577771089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90946693021356031718514059 136420039532034047577771089)
    ·
      refine ⟨102315029649025535683328317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136420039532034047577771089 102315029649025535683328317)
      ·
        refine ⟨38368136118384575881248119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102315029649025535683328317 38368136118384575881248119)
        ·
          refine ⟨57552204177576863821872179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38368136118384575881248119 57552204177576863821872179)
          ·
            refine ⟨86328306266365295732808269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57552204177576863821872179 86328306266365295732808269)
            ·
              refine ⟨32373114849886985899803101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86328306266365295732808269 32373114849886985899803101)
              ·
                refine ⟨12139918068707619712426163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32373114849886985899803101 12139918068707619712426163)
                ·
                  refine ⟨18209877103061429568639245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12139918068707619712426163 18209877103061429568639245)
                  ·
                    refine ⟨6828703913648036088239717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18209877103061429568639245 6828703913648036088239717)
                    ·
                      refine ⟨1280381983809006766544947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6828703913648036088239717 1280381983809006766544947)
                      ·
                        rfl

theorem cell23_2493535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2493535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493535 prefixEnd_2493535 := by exact prefixLift 2493535
  have htrace : WordTrace (prefixWord ++ tailWord_2493535) baseStart_2493535 baseEnd_2493535 := by
    simpa [prefixWord, tailWord_2493535, baseEnd_2493535] using wordTrace_append hprefix tailTrace_2493535
  have hstable : (prefixWord ++ tailWord_2493535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493535).length < 2 ^ (prefixWord ++ tailWord_2493535).sum := by decide
  have hdescent : baseEnd_2493535 < baseStart_2493535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493552 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_2493552 : Nat := 118140960795 + 2493552 * 2 ^ 59
def prefixEnd_2493552 : Nat := 4983230072969 + 3 ^ 40 * 2493552 * 2
def baseEnd_2493552 : Nat := 1280390712980133200032369

theorem tailTrace_2493552 : CollatzResearch.WordTrace tailWord_2493552 prefixEnd_2493552 1280390712980133200032369 := by
  unfold tailWord_2493552
  simp only [CollatzResearch.WordTrace]
  refine ⟨45473656531147221810941455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60631542041529629081255273 45473656531147221810941455)
  ·
    refine ⟨68210484796720832716412183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45473656531147221810941455 68210484796720832716412183)
    ·
      refine ⟨102315727195081249074618275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68210484796720832716412183 102315727195081249074618275)
      ·
        refine ⟨153473590792621873611927413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102315727195081249074618275 153473590792621873611927413)
        ·
          refine ⟨14388149136808300651118195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153473590792621873611927413 14388149136808300651118195)
          ·
            refine ⟨21582223705212450976677293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14388149136808300651118195 21582223705212450976677293)
            ·
              refine ⟨8093333889454669116253985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21582223705212450976677293 8093333889454669116253985)
              ·
                refine ⟨6070000417091001837190489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8093333889454669116253985 6070000417091001837190489)
                ·
                  refine ⟨4552500312818251377892867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6070000417091001837190489 4552500312818251377892867)
                  ·
                    refine ⟨6828750469227377066839301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4552500312818251377892867 6828750469227377066839301)
                    ·
                      refine ⟨1280390712980133200032369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6828750469227377066839301 1280390712980133200032369)
                      ·
                        rfl

theorem cell23_2493552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_2493552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493552 prefixEnd_2493552 := by exact prefixLift 2493552
  have htrace : WordTrace (prefixWord ++ tailWord_2493552) baseStart_2493552 baseEnd_2493552 := by
    simpa [prefixWord, tailWord_2493552, baseEnd_2493552] using wordTrace_append hprefix tailTrace_2493552
  have hstable : (prefixWord ++ tailWord_2493552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493552).length < 2 ^ (prefixWord ++ tailWord_2493552).sum := by decide
  have hdescent : baseEnd_2493552 < baseStart_2493552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493555 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3]
def baseStart_2493555 : Nat := 118140960795 + 2493555 * 2 ^ 59
def prefixEnd_2493555 : Nat := 4983230072969 + 3 ^ 40 * 2493555 * 2
def baseEnd_2493555 : Nat := 1280392253422096688294855

theorem tailTrace_2493555 : CollatzResearch.WordTrace tailWord_2493555 prefixEnd_2493555 1280392253422096688294855 := by
  unfold tailWord_2493555
  simp only [CollatzResearch.WordTrace]
  refine ⟨90947422481283575134242119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60631614987522383422828079 90947422481283575134242119)
  ·
    refine ⟨136421133721925362701363179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90947422481283575134242119 136421133721925362701363179)
    ·
      refine ⟨204631700582888044052044769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136421133721925362701363179 204631700582888044052044769)
      ·
        refine ⟨153473775437166033039033577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204631700582888044052044769 153473775437166033039033577)
        ·
          refine ⟨115105331577874524779275183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153473775437166033039033577 115105331577874524779275183)
          ·
            refine ⟨172657997366811787168912775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115105331577874524779275183 172657997366811787168912775)
            ·
              refine ⟨258986996050217680753369163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172657997366811787168912775 258986996050217680753369163)
              ·
                refine ⟨388480494075326521130053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258986996050217680753369163 388480494075326521130053745)
                ·
                  refine ⟨291360370556494890847540309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388480494075326521130053745 291360370556494890847540309)
                  ·
                    refine ⟨3414379342458924502119613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 291360370556494890847540309 3414379342458924502119613)
                    ·
                      refine ⟨1280392253422096688294855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3414379342458924502119613 1280392253422096688294855)
                      ·
                        rfl

theorem cell23_2493555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_2493555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493555 prefixEnd_2493555 := by exact prefixLift 2493555
  have htrace : WordTrace (prefixWord ++ tailWord_2493555) baseStart_2493555 baseEnd_2493555 := by
    simpa [prefixWord, tailWord_2493555, baseEnd_2493555] using wordTrace_append hprefix tailTrace_2493555
  have hstable : (prefixWord ++ tailWord_2493555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493555).length < 2 ^ (prefixWord ++ tailWord_2493555).sum := by decide
  have hdescent : baseEnd_2493555 < baseStart_2493555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493613 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2493613 : Nat := 118140960795 + 2493613 * 2 ^ 59
def prefixEnd_2493613 : Nat := 4983230072969 + 3 ^ 40 * 2493613 * 2
def baseEnd_2493613 : Nat := 426807345100019153789863

theorem tailTrace_2493613 : CollatzResearch.WordTrace tailWord_2493613 prefixEnd_2493613 426807345100019153789863 := by
  unfold tailWord_2493613
  simp only [CollatzResearch.WordTrace]
  refine ⟨90949537915073451039853493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60633025276715634026568995 90949537915073451039853493)
  ·
    refine ⟨8526519179538136034986265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90949537915073451039853493 8526519179538136034986265)
    ·
      refine ⟨6394889384653602026239699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8526519179538136034986265 6394889384653602026239699)
      ·
        refine ⟨9592334076980403039359549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394889384653602026239699 9592334076980403039359549)
        ·
          refine ⟨3597125278867651139759831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9592334076980403039359549 3597125278867651139759831)
          ·
            refine ⟨5395687918301476709639747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597125278867651139759831 5395687918301476709639747)
            ·
              refine ⟨8093531877452215064459621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395687918301476709639747 8093531877452215064459621)
              ·
                refine ⟨1517537227022290324586179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8093531877452215064459621 1517537227022290324586179)
                ·
                  refine ⟨2276305840533435486879269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517537227022290324586179 2276305840533435486879269)
                  ·
                    refine ⟨426807345100019153789863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2276305840533435486879269 426807345100019153789863)
                    ·
                      rfl

theorem cell23_2493613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2493613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493613 prefixEnd_2493613 := by exact prefixLift 2493613
  have htrace : WordTrace (prefixWord ++ tailWord_2493613) baseStart_2493613 baseEnd_2493613 := by
    simpa [prefixWord, tailWord_2493613, baseEnd_2493613] using wordTrace_append hprefix tailTrace_2493613
  have hstable : (prefixWord ++ tailWord_2493613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493613).length < 2 ^ (prefixWord ++ tailWord_2493613).sum := by decide
  have hdescent : baseEnd_2493613 < baseStart_2493613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493629 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_2493629 : Nat := 118140960795 + 2493629 * 2 ^ 59
def prefixEnd_2493629 : Nat := 4983230072969 + 3 ^ 40 * 2493629 * 2
def baseEnd_2493629 : Nat := 1280430250990529398769515

theorem tailTrace_2493629 : CollatzResearch.WordTrace tailWord_2493629 prefixEnd_2493629 1280430250990529398769515 := by
  unfold tailWord_2493629
  simp only [CollatzResearch.WordTrace]
  refine ⟨90950121483015485772435941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60633414322010323848290627 90950121483015485772435941)
  ·
    refine ⟨17053147778065403582331739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90950121483015485772435941 17053147778065403582331739)
    ·
      refine ⟨25579721667098105373497609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053147778065403582331739 25579721667098105373497609)
      ·
        refine ⟨19184791250323579030123207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25579721667098105373497609 19184791250323579030123207)
        ·
          refine ⟨28777186875485368545184811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19184791250323579030123207 28777186875485368545184811)
          ·
            refine ⟨43165780313228052817777217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28777186875485368545184811 43165780313228052817777217)
            ·
              refine ⟨32374335234921039613332913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43165780313228052817777217 32374335234921039613332913)
              ·
                refine ⟨24280751426190779709999685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32374335234921039613332913 24280751426190779709999685)
                ·
                  refine ⟨4552640892410771195624941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24280751426190779709999685 4552640892410771195624941)
                  ·
                    refine ⟨1707240334654039198359353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4552640892410771195624941 1707240334654039198359353)
                    ·
                      refine ⟨1280430250990529398769515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707240334654039198359353 1280430250990529398769515)
                      ·
                        rfl

theorem cell23_2493629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_2493629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493629 prefixEnd_2493629 := by exact prefixLift 2493629
  have htrace : WordTrace (prefixWord ++ tailWord_2493629) baseStart_2493629 baseEnd_2493629 := by
    simpa [prefixWord, tailWord_2493629, baseEnd_2493629] using wordTrace_append hprefix tailTrace_2493629
  have hstable : (prefixWord ++ tailWord_2493629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493629).length < 2 ^ (prefixWord ++ tailWord_2493629).sum := by decide
  have hdescent : baseEnd_2493629 < baseStart_2493629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493646 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_2493646 : Nat := 118140960795 + 2493646 * 2 ^ 59
def prefixEnd_2493646 : Nat := 4983230072969 + 3 ^ 40 * 2493646 * 2
def baseEnd_2493646 : Nat := 1280438980161655832256937

theorem tailTrace_2493646 : CollatzResearch.WordTrace tailWord_2493646 prefixEnd_2493646 1280438980161655832256937 := by
  unfold tailWord_2493646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368842690494237209475599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60633827682635931783869861 11368842690494237209475599)
  ·
    refine ⟨17053264035741355814213399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11368842690494237209475599 17053264035741355814213399)
    ·
      refine ⟨25579896053612033721320099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053264035741355814213399 25579896053612033721320099)
      ·
        refine ⟨38369844080418050581980149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25579896053612033721320099 38369844080418050581980149)
        ·
          refine ⟨3597172882539192242060639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38369844080418050581980149 3597172882539192242060639)
          ·
            refine ⟨5395759323808788363090959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597172882539192242060639 5395759323808788363090959)
            ·
              refine ⟨8093638985713182544636439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395759323808788363090959 8093638985713182544636439)
              ·
                refine ⟨12140458478569773816954659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8093638985713182544636439 12140458478569773816954659)
                ·
                  refine ⟨18210687717854660725431989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12140458478569773816954659 18210687717854660725431989)
                  ·
                    refine ⟨1707251973548874443009249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18210687717854660725431989 1707251973548874443009249)
                    ·
                      refine ⟨1280438980161655832256937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707251973548874443009249 1280438980161655832256937)
                      ·
                        rfl

theorem cell23_2493646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_2493646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493646 prefixEnd_2493646 := by exact prefixLift 2493646
  have htrace : WordTrace (prefixWord ++ tailWord_2493646) baseStart_2493646 baseEnd_2493646 := by
    simpa [prefixWord, tailWord_2493646, baseEnd_2493646] using wordTrace_append hprefix tailTrace_2493646
  have hstable : (prefixWord ++ tailWord_2493646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493646).length < 2 ^ (prefixWord ++ tailWord_2493646).sum := by decide
  have hdescent : baseEnd_2493646 < baseStart_2493646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493653 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2493653 : Nat := 118140960795 + 2493653 * 2 ^ 59
def prefixEnd_2493653 : Nat := 4983230072969 + 3 ^ 40 * 2493653 * 2
def baseEnd_2493653 : Nat := 1280442574526237304869405

theorem tailTrace_2493653 : CollatzResearch.WordTrace tailWord_2493653 prefixEnd_2493653 1280442574526237304869405 := by
  unfold tailWord_2493653
  simp only [CollatzResearch.WordTrace]
  refine ⟨90950996834928537871309613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60633997889952358580873075 90950996834928537871309613)
  ·
    refine ⟨34106623813098201701741105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90950996834928537871309613 34106623813098201701741105)
    ·
      refine ⟨25579967859823651276305829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34106623813098201701741105 25579967859823651276305829)
      ·
        refine ⟨4796243973716934614307343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25579967859823651276305829 4796243973716934614307343)
        ·
          refine ⟨7194365960575401921461015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796243973716934614307343 7194365960575401921461015)
          ·
            refine ⟨10791548940863102882191523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194365960575401921461015 10791548940863102882191523)
            ·
              refine ⟨16187323411294654323287285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10791548940863102882191523 16187323411294654323287285)
              ·
                refine ⟨1517561569808873842808183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16187323411294654323287285 1517561569808873842808183)
                ·
                  refine ⟨2276342354713310764212275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517561569808873842808183 2276342354713310764212275)
                  ·
                    refine ⟨3414513532069966146318413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2276342354713310764212275 3414513532069966146318413)
                    ·
                      refine ⟨1280442574526237304869405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3414513532069966146318413 1280442574526237304869405)
                      ·
                        rfl

theorem cell23_2493653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2493653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493653 prefixEnd_2493653 := by exact prefixLift 2493653
  have htrace : WordTrace (prefixWord ++ tailWord_2493653) baseStart_2493653 baseEnd_2493653 := by
    simpa [prefixWord, tailWord_2493653, baseEnd_2493653] using wordTrace_append hprefix tailTrace_2493653
  have hstable : (prefixWord ++ tailWord_2493653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493653).length < 2 ^ (prefixWord ++ tailWord_2493653).sum := by decide
  have hdescent : baseEnd_2493653 < baseStart_2493653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493672 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2493672 : Nat := 118140960795 + 2493672 * 2 ^ 59
def prefixEnd_2493672 : Nat := 4983230072969 + 3 ^ 40 * 2493672 * 2
def baseEnd_2493672 : Nat := 1280452330658672730531817

theorem tailTrace_2493672 : CollatzResearch.WordTrace tailWord_2493672 prefixEnd_2493672 1280452330658672730531817 := by
  unfold tailWord_2493672
  simp only [CollatzResearch.WordTrace]
  refine ⟨45475844910929852058125635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60634459881239802744167513 45475844910929852058125635)
  ·
    refine ⟨68213767366394778087188453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45475844910929852058125635 68213767366394778087188453)
    ·
      refine ⟨12790081381199020891347835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68213767366394778087188453 12790081381199020891347835)
      ·
        refine ⟨19185122071798531337021753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12790081381199020891347835 19185122071798531337021753)
        ·
          refine ⟨14388841553848898502766315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19185122071798531337021753 14388841553848898502766315)
          ·
            refine ⟨21583262330773347754149473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14388841553848898502766315 21583262330773347754149473)
            ·
              refine ⟨16187446748080010815612105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21583262330773347754149473 16187446748080010815612105)
              ·
                refine ⟨12140585061060008111709079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16187446748080010815612105 12140585061060008111709079)
                ·
                  refine ⟨18210877591590012167563619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12140585061060008111709079 18210877591590012167563619)
                  ·
                    refine ⟨27316316387385018251345429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18210877591590012167563619 27316316387385018251345429)
                    ·
                      refine ⟨1280452330658672730531817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27316316387385018251345429 1280452330658672730531817)
                      ·
                        rfl

theorem cell23_2493672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2493672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493672 prefixEnd_2493672 := by exact prefixLift 2493672
  have htrace : WordTrace (prefixWord ++ tailWord_2493672) baseStart_2493672 baseEnd_2493672 := by
    simpa [prefixWord, tailWord_2493672, baseEnd_2493672] using wordTrace_append hprefix tailTrace_2493672
  have hstable : (prefixWord ++ tailWord_2493672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493672).length < 2 ^ (prefixWord ++ tailWord_2493672).sum := by decide
  have hdescent : baseEnd_2493672 < baseStart_2493672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493676 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_2493676 : Nat := 118140960795 + 2493676 * 2 ^ 59
def prefixEnd_2493676 : Nat := 4983230072969 + 3 ^ 40 * 2493676 * 2
def baseEnd_2493676 : Nat := 1280454384581290714881799

theorem tailTrace_2493676 : CollatzResearch.WordTrace tailWord_2493676 prefixEnd_2493676 1280454384581290714881799 := by
  unfold tailWord_2493676
  simp only [CollatzResearch.WordTrace]
  refine ⟨45475917856922606399698441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60634557142563475199597921 45475917856922606399698441)
  ·
    refine ⟨34106938392691954799773831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45475917856922606399698441 34106938392691954799773831)
    ·
      refine ⟨51160407589037932199660747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34106938392691954799773831 51160407589037932199660747)
      ·
        refine ⟨76740611383556898299491121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51160407589037932199660747 76740611383556898299491121)
        ·
          refine ⟨57555458537667673724618341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76740611383556898299491121 57555458537667673724618341)
          ·
            refine ⟨10791648475812688823365939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57555458537667673724618341 10791648475812688823365939)
            ·
              refine ⟨16187472713719033235048909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10791648475812688823365939 16187472713719033235048909)
              ·
                refine ⟨6070302267644637463143341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16187472713719033235048909 6070302267644637463143341)
                ·
                  refine ⟨2276363350366739048678753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6070302267644637463143341 2276363350366739048678753)
                  ·
                    refine ⟨1707272512775054286509065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276363350366739048678753 1707272512775054286509065)
                    ·
                      refine ⟨1280454384581290714881799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707272512775054286509065 1280454384581290714881799)
                      ·
                        rfl

theorem cell23_2493676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_2493676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493676 prefixEnd_2493676 := by exact prefixLift 2493676
  have htrace : WordTrace (prefixWord ++ tailWord_2493676) baseStart_2493676 baseEnd_2493676 := by
    simpa [prefixWord, tailWord_2493676, baseEnd_2493676] using wordTrace_append hprefix tailTrace_2493676
  have hstable : (prefixWord ++ tailWord_2493676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493676).length < 2 ^ (prefixWord ++ tailWord_2493676).sum := by decide
  have hdescent : baseEnd_2493676 < baseStart_2493676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493679 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_2493679 : Nat := 118140960795 + 2493679 * 2 ^ 59
def prefixEnd_2493679 : Nat := 4983230072969 + 3 ^ 40 * 2493679 * 2
def baseEnd_2493679 : Nat := 1280455925023254203144285

theorem tailTrace_2493679 : CollatzResearch.WordTrace tailWord_2493679 prefixEnd_2493679 1280455925023254203144285 := by
  unfold tailWord_2493679
  simp only [CollatzResearch.WordTrace]
  refine ⟨90951945132834344311756091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60634630088556229541170727 90951945132834344311756091)
  ·
    refine ⟨136427917699251516467634137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90951945132834344311756091 136427917699251516467634137)
    ·
      refine ⟨102320938274438637350725603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136427917699251516467634137 102320938274438637350725603)
      ·
        refine ⟨153481407411657956026088405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102320938274438637350725603 153481407411657956026088405)
        ·
          refine ⟨3597220486210733344361447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 153481407411657956026088405 3597220486210733344361447)
          ·
            refine ⟨5395830729316100016542171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597220486210733344361447 5395830729316100016542171)
            ·
              refine ⟨8093746093974150024813257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395830729316100016542171 8093746093974150024813257)
              ·
                refine ⟨6070309570480612518609943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8093746093974150024813257 6070309570480612518609943)
                ·
                  refine ⟨9105464355720918777914915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6070309570480612518609943 9105464355720918777914915)
                  ·
                    refine ⟨13658196533581378166872373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9105464355720918777914915 13658196533581378166872373)
                    ·
                      refine ⟨1280455925023254203144285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13658196533581378166872373 1280455925023254203144285)
                      ·
                        rfl

theorem cell23_2493679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_2493679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493679 prefixEnd_2493679 := by exact prefixLift 2493679
  have htrace : WordTrace (prefixWord ++ tailWord_2493679) baseStart_2493679 baseEnd_2493679 := by
    simpa [prefixWord, tailWord_2493679, baseEnd_2493679] using wordTrace_append hprefix tailTrace_2493679
  have hstable : (prefixWord ++ tailWord_2493679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493679).length < 2 ^ (prefixWord ++ tailWord_2493679).sum := by decide
  have hdescent : baseEnd_2493679 < baseStart_2493679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493699 : List Nat := [1, 1, 1, 3, 2, 6, 2, 7]
def baseStart_2493699 : Nat := 118140960795 + 2493699 * 2 ^ 59
def prefixEnd_2493699 : Nat := 4983230072969 + 3 ^ 40 * 2493699 * 2
def baseEnd_2493699 : Nat := 47424673875420152773859

theorem tailTrace_2493699 : CollatzResearch.WordTrace tailWord_2493699 prefixEnd_2493699 47424673875420152773859 := by
  unfold tailWord_2493699
  simp only [CollatzResearch.WordTrace]
  refine ⟨90952674592761887727484151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60635116395174591818322767 90952674592761887727484151)
  ·
    refine ⟨136429011889142831591226227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90952674592761887727484151 136429011889142831591226227)
    ·
      refine ⟨204643517833714247386839341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136429011889142831591226227 204643517833714247386839341)
      ·
        refine ⟨76741319187642842770064753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204643517833714247386839341 76741319187642842770064753)
        ·
          refine ⟨57555989390732132077548565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76741319187642842770064753 57555989390732132077548565)
          ·
            refine ⟨2697937002690568691135089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57555989390732132077548565 2697937002690568691135089)
            ·
              refine ⟨2023452752017926518351317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697937002690568691135089 2023452752017926518351317)
              ·
                refine ⟨47424673875420152773859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2023452752017926518351317 47424673875420152773859)
                ·
                  rfl

theorem cell23_2493699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 7].length) (baseStart_2493699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493699 prefixEnd_2493699 := by exact prefixLift 2493699
  have htrace : WordTrace (prefixWord ++ tailWord_2493699) baseStart_2493699 baseEnd_2493699 := by
    simpa [prefixWord, tailWord_2493699, baseEnd_2493699] using wordTrace_append hprefix tailTrace_2493699
  have hstable : (prefixWord ++ tailWord_2493699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493699).length < 2 ^ (prefixWord ++ tailWord_2493699).sum := by decide
  have hdescent : baseEnd_2493699 < baseStart_2493699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493710 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2493710 : Nat := 118140960795 + 2493710 * 2 ^ 59
def prefixEnd_2493710 : Nat := 4983230072969 + 3 ^ 40 * 2493710 * 2
def baseEnd_2493710 : Nat := 1280471842923543581856643

theorem tailTrace_2493710 : CollatzResearch.WordTrace tailWord_2493710 prefixEnd_2493710 1280471842923543581856643 := by
  unfold tailWord_2493710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369134474465254575766823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60635383863814691070756389 11369134474465254575766823)
  ·
    refine ⟨17053701711697881863650235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11369134474465254575766823 17053701711697881863650235)
    ·
      refine ⟨25580552567546822795475353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053701711697881863650235 25580552567546822795475353)
      ·
        refine ⟨19185414425660117096606515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25580552567546822795475353 19185414425660117096606515)
        ·
          refine ⟨28778121638490175644909773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19185414425660117096606515 28778121638490175644909773)
          ·
            refine ⟨10791795614433815866841165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28778121638490175644909773 10791795614433815866841165)
            ·
              refine ⟨4046923355412680950065437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10791795614433815866841165 4046923355412680950065437)
              ·
                refine ⟨1517596258279755356274539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4046923355412680950065437 1517596258279755356274539)
                ·
                  refine ⟨2276394387419633034411809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517596258279755356274539 2276394387419633034411809)
                  ·
                    refine ⟨1707295790564724775808857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276394387419633034411809 1707295790564724775808857)
                    ·
                      refine ⟨1280471842923543581856643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707295790564724775808857 1280471842923543581856643)
                      ·
                        rfl

theorem cell23_2493710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2493710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493710 prefixEnd_2493710 := by exact prefixLift 2493710
  have htrace : WordTrace (prefixWord ++ tailWord_2493710) baseStart_2493710 baseEnd_2493710 := by
    simpa [prefixWord, tailWord_2493710, baseEnd_2493710] using wordTrace_append hprefix tailTrace_2493710
  have hstable : (prefixWord ++ tailWord_2493710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493710).length < 2 ^ (prefixWord ++ tailWord_2493710).sum := by decide
  have hdescent : baseEnd_2493710 < baseStart_2493710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493727 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 1, 2, 2]
def baseStart_2493727 : Nat := 118140960795 + 2493727 * 2 ^ 59
def prefixEnd_2493727 : Nat := 4983230072969 + 3 ^ 40 * 2493727 * 2
def baseEnd_2493727 : Nat := 1280480572094670015344065

theorem tailTrace_2493727 : CollatzResearch.WordTrace tailWord_2493727 prefixEnd_2493727 1280480572094670015344065 := by
  unfold tailWord_2493727
  simp only [CollatzResearch.WordTrace]
  refine ⟨90953695836660448509503435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60635797224440299006335623 90953695836660448509503435)
  ·
    refine ⟨136430543754990672764255153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90953695836660448509503435 136430543754990672764255153)
    ·
      refine ⟨102322907816243004573191365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136430543754990672764255153 102322907816243004573191365)
      ·
        refine ⟨19185545215545563357473381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102322907816243004573191365 19185545215545563357473381)
        ·
          refine ⟨3597289727914793129526259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19185545215545563357473381 3597289727914793129526259)
          ·
            refine ⟨5395934591872189694289389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597289727914793129526259 5395934591872189694289389)
            ·
              refine ⟨2023475471952071135358521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5395934591872189694289389 2023475471952071135358521)
              ·
                refine ⟨1517606603964053351518891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023475471952071135358521 1517606603964053351518891)
                ·
                  refine ⟨2276409905946080027278337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517606603964053351518891 2276409905946080027278337)
                  ·
                    refine ⟨1707307429459560020458753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276409905946080027278337 1707307429459560020458753)
                    ·
                      refine ⟨1280480572094670015344065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707307429459560020458753 1280480572094670015344065)
                      ·
                        rfl

theorem cell23_2493727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_2493727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493727 prefixEnd_2493727 := by exact prefixLift 2493727
  have htrace : WordTrace (prefixWord ++ tailWord_2493727) baseStart_2493727 baseEnd_2493727 := by
    simpa [prefixWord, tailWord_2493727, baseEnd_2493727] using wordTrace_append hprefix tailTrace_2493727
  have hstable : (prefixWord ++ tailWord_2493727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493727).length < 2 ^ (prefixWord ++ tailWord_2493727).sum := by decide
  have hdescent : baseEnd_2493727 < baseStart_2493727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493753 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2493753 : Nat := 118140960795 + 2493753 * 2 ^ 59
def prefixEnd_2493753 : Nat := 4983230072969 + 3 ^ 40 * 2493753 * 2
def baseEnd_2493753 : Nat := 1280493922591686913618945

theorem tailTrace_2493753 : CollatzResearch.WordTrace tailWord_2493753 prefixEnd_2493753 1280493922591686913618945 := by
  unfold tailWord_2493753
  simp only [CollatzResearch.WordTrace]
  refine ⟨90954644134566254949949913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60636429423044169966633275 90954644134566254949949913)
  ·
    refine ⟨68215983100924691212462435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90954644134566254949949913 68215983100924691212462435)
    ·
      refine ⟨102323974651387036818693653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68215983100924691212462435 102323974651387036818693653)
      ·
        refine ⟨4796436311783767350876265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102323974651387036818693653 4796436311783767350876265)
        ·
          refine ⟨3597327233837825513157199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4796436311783767350876265 3597327233837825513157199)
          ·
            refine ⟨5395990850756738269735799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597327233837825513157199 5395990850756738269735799)
            ·
              refine ⟨8093986276135107404603699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395990850756738269735799 8093986276135107404603699)
              ·
                refine ⟨12140979414202661106905549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8093986276135107404603699 12140979414202661106905549)
                ·
                  refine ⟨4552867280325997915089581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12140979414202661106905549 4552867280325997915089581)
                  ·
                    refine ⟨1707325230122249218158593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4552867280325997915089581 1707325230122249218158593)
                    ·
                      refine ⟨1280493922591686913618945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707325230122249218158593 1280493922591686913618945)
                      ·
                        rfl

theorem cell23_2493753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2493753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493753 prefixEnd_2493753 := by exact prefixLift 2493753
  have htrace : WordTrace (prefixWord ++ tailWord_2493753) baseStart_2493753 baseEnd_2493753 := by
    simpa [prefixWord, tailWord_2493753, baseEnd_2493753] using wordTrace_append hprefix tailTrace_2493753
  have hstable : (prefixWord ++ tailWord_2493753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493753).length < 2 ^ (prefixWord ++ tailWord_2493753).sum := by decide
  have hdescent : baseEnd_2493753 < baseStart_2493753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493783 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_2493783 : Nat := 118140960795 + 2493783 * 2 ^ 59
def prefixEnd_2493783 : Nat := 4983230072969 + 3 ^ 40 * 2493783 * 2
def baseEnd_2493783 : Nat := 1280509327011321796243807

theorem tailTrace_2493783 : CollatzResearch.WordTrace tailWord_2493783 prefixEnd_2493783 1280509327011321796243807 := by
  unfold tailWord_2493783
  simp only [CollatzResearch.WordTrace]
  refine ⟨90955738324457570073542003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60637158882971713382361335 90955738324457570073542003)
  ·
    refine ⟨136433607486686355110313005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90955738324457570073542003 136433607486686355110313005)
    ·
      refine ⟨51162602807507383166367377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136433607486686355110313005 51162602807507383166367377)
      ·
        refine ⟨38371952105630537374775533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51162602807507383166367377 38371952105630537374775533)
        ·
          refine ⟨14389482039611451515540825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38371952105630537374775533 14389482039611451515540825)
          ·
            refine ⟨10792111529708588636655619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14389482039611451515540825 10792111529708588636655619)
            ·
              refine ⟨16188167294562882954983429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10792111529708588636655619 16188167294562882954983429)
              ·
                refine ⟨3035281367730540554059393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16188167294562882954983429 3035281367730540554059393)
                ·
                  refine ⟨2276461025797905415544545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3035281367730540554059393 2276461025797905415544545)
                  ·
                    refine ⟨1707345769348429061658409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276461025797905415544545 1707345769348429061658409)
                    ·
                      refine ⟨1280509327011321796243807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707345769348429061658409 1280509327011321796243807)
                      ·
                        rfl

theorem cell23_2493783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_2493783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493783 prefixEnd_2493783 := by exact prefixLift 2493783
  have htrace : WordTrace (prefixWord ++ tailWord_2493783) baseStart_2493783 baseEnd_2493783 := by
    simpa [prefixWord, tailWord_2493783, baseEnd_2493783] using wordTrace_append hprefix tailTrace_2493783
  have hstable : (prefixWord ++ tailWord_2493783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493783).length < 2 ^ (prefixWord ++ tailWord_2493783).sum := by decide
  have hdescent : baseEnd_2493783 < baseStart_2493783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493856 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2]
def baseStart_2493856 : Nat := 118140960795 + 2493856 * 2 ^ 59
def prefixEnd_2493856 : Nat := 4983230072969 + 3 ^ 40 * 2493856 * 2
def baseEnd_2493856 : Nat := 1280546811099100010630971

theorem tailTrace_2493856 : CollatzResearch.WordTrace tailWord_2493856 prefixEnd_2493856 1280546811099100010630971 := by
  unfold tailWord_2493856
  simp only [CollatzResearch.WordTrace]
  refine ⟨45479200426596551770474711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60638933902128735693966281 45479200426596551770474711)
  ·
    refine ⟨68218800639894827655712067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45479200426596551770474711 68218800639894827655712067)
    ·
      refine ⟨102328200959842241483568101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68218800639894827655712067 102328200959842241483568101)
      ·
        refine ⟨19186537679970420278169019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102328200959842241483568101 19186537679970420278169019)
        ·
          refine ⟨28779806519955630417253529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19186537679970420278169019 28779806519955630417253529)
          ·
            refine ⟨21584854889966722812940147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28779806519955630417253529 21584854889966722812940147)
            ·
              refine ⟨32377282334950084219410221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21584854889966722812940147 32377282334950084219410221)
              ·
                refine ⟨12141480875606281582278833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32377282334950084219410221 12141480875606281582278833)
                ·
                  refine ⟨9106110656704711186709125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12141480875606281582278833 9106110656704711186709125)
                  ·
                    refine ⟨1707395748132133347507961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9106110656704711186709125 1707395748132133347507961)
                    ·
                      refine ⟨1280546811099100010630971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707395748132133347507961 1280546811099100010630971)
                      ·
                        rfl

theorem cell23_2493856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_2493856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493856 prefixEnd_2493856 := by exact prefixLift 2493856
  have htrace : WordTrace (prefixWord ++ tailWord_2493856) baseStart_2493856 baseEnd_2493856 := by
    simpa [prefixWord, tailWord_2493856, baseEnd_2493856] using wordTrace_append hprefix tailTrace_2493856
  have hstable : (prefixWord ++ tailWord_2493856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493856).length < 2 ^ (prefixWord ++ tailWord_2493856).sum := by decide
  have hdescent : baseEnd_2493856 < baseStart_2493856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493859 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3]
def baseStart_2493859 : Nat := 118140960795 + 2493859 * 2 ^ 59
def prefixEnd_2493859 : Nat := 4983230072969 + 3 ^ 40 * 2493859 * 2
def baseEnd_2493859 : Nat := 1280548351541063498893457

theorem tailTrace_2493859 : CollatzResearch.WordTrace tailWord_2493859 prefixEnd_2493859 1280548351541063498893457 := by
  unfold tailWord_2493859
  simp only [CollatzResearch.WordTrace]
  refine ⟨90958510272182235053308631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60639006848121490035539087 90958510272182235053308631)
  ·
    refine ⟨136437765408273352579962947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90958510272182235053308631 136437765408273352579962947)
    ·
      refine ⟨204656648112410028869944421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136437765408273352579962947 204656648112410028869944421)
      ·
        refine ⟨38373121521076880413114579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204656648112410028869944421 38373121521076880413114579)
        ·
          refine ⟨57559682281615320619671869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38373121521076880413114579 57559682281615320619671869)
          ·
            refine ⟨21584880855605745232376951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57559682281615320619671869 21584880855605745232376951)
            ·
              refine ⟨32377321283408617848565427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21584880855605745232376951 32377321283408617848565427)
              ·
                refine ⟨48565981925112926772848141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32377321283408617848565427 48565981925112926772848141)
                ·
                  refine ⟨18212243221917347539818053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48565981925112926772848141 18212243221917347539818053)
                  ·
                    refine ⟨3414795604109502663715885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18212243221917347539818053 3414795604109502663715885)
                    ·
                      refine ⟨1280548351541063498893457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3414795604109502663715885 1280548351541063498893457)
                      ·
                        rfl

theorem cell23_2493859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_2493859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493859 prefixEnd_2493859 := by exact prefixLift 2493859
  have htrace : WordTrace (prefixWord ++ tailWord_2493859) baseStart_2493859 baseEnd_2493859 := by
    simpa [prefixWord, tailWord_2493859, baseEnd_2493859] using wordTrace_append hprefix tailTrace_2493859
  have hstable : (prefixWord ++ tailWord_2493859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493859).length < 2 ^ (prefixWord ++ tailWord_2493859).sum := by decide
  have hdescent : baseEnd_2493859 < baseStart_2493859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493913 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 6]
def baseStart_2493913 : Nat := 118140960795 + 2493913 * 2 ^ 59
def prefixEnd_2493913 : Nat := 4983230072969 + 3 ^ 40 * 2493913 * 2
def baseEnd_2493913 : Nat := 142286231055156254179801

theorem tailTrace_2493913 : CollatzResearch.WordTrace tailWord_2493913 prefixEnd_2493913 142286231055156254179801 := by
  unfold tailWord_2493913
  simp only [CollatzResearch.WordTrace]
  refine ⟨90960479813986602275774393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60640319875991068183849595 90960479813986602275774393)
  ·
    refine ⟨68220359860489951706830795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90960479813986602275774393 68220359860489951706830795)
    ·
      refine ⟨102330539790734927560246193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68220359860489951706830795 102330539790734927560246193)
      ·
        refine ⟨76747904843051195670184645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102330539790734927560246193 76747904843051195670184645)
        ·
          refine ⟨14390232158072099188159621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76747904843051195670184645 14390232158072099188159621)
          ·
            refine ⟨2698168529638518597779929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14390232158072099188159621 2698168529638518597779929)
            ·
              refine ⟨2023626397228888948334947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698168529638518597779929 2023626397228888948334947)
              ·
                refine ⟨3035439595843333422502421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023626397228888948334947 3035439595843333422502421)
                ·
                  refine ⟨142286231055156254179801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3035439595843333422502421 142286231055156254179801)
                  ·
                    rfl

theorem cell23_2493913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 6].length) (baseStart_2493913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493913 prefixEnd_2493913 := by exact prefixLift 2493913
  have htrace : WordTrace (prefixWord ++ tailWord_2493913) baseStart_2493913 baseEnd_2493913 := by
    simpa [prefixWord, tailWord_2493913, baseEnd_2493913] using wordTrace_append hprefix tailTrace_2493913
  have hstable : (prefixWord ++ tailWord_2493913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493913).length < 2 ^ (prefixWord ++ tailWord_2493913).sum := by decide
  have hdescent : baseEnd_2493913 < baseStart_2493913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493973 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2493973 : Nat := 118140960795 + 2493973 * 2 ^ 59
def prefixEnd_2493973 : Nat := 4983230072969 + 3 ^ 40 * 2493973 * 2
def baseEnd_2493973 : Nat := 426868962778558684289311

theorem tailTrace_2493973 : CollatzResearch.WordTrace tailWord_2493973 prefixEnd_2493973 426868962778558684289311 := by
  unfold tailWord_2493973
  simp only [CollatzResearch.WordTrace]
  refine ⟨90962668193769232522958573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60641778795846155015305715 90962668193769232522958573)
  ·
    refine ⟨34111000572663462196109465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90962668193769232522958573 34111000572663462196109465)
    ·
      refine ⟨25583250429497596647082099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34111000572663462196109465 25583250429497596647082099)
      ·
        refine ⟨38374875644246394970623149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25583250429497596647082099 38374875644246394970623149)
        ·
          refine ⟨14390578366592398113983681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38374875644246394970623149 14390578366592398113983681)
          ·
            refine ⟨10792933774944298585487761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14390578366592398113983681 10792933774944298585487761)
            ·
              refine ⟨8094700331208223939115821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10792933774944298585487761 8094700331208223939115821)
              ·
                refine ⟨3035512624203083977168433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8094700331208223939115821 3035512624203083977168433)
                ·
                  refine ⟨2276634468152312982876325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3035512624203083977168433 2276634468152312982876325)
                  ·
                    refine ⟨426868962778558684289311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2276634468152312982876325 426868962778558684289311)
                    ·
                      rfl

theorem cell23_2493973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2493973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493973 prefixEnd_2493973 := by exact prefixLift 2493973
  have htrace : WordTrace (prefixWord ++ tailWord_2493973) baseStart_2493973 baseEnd_2493973 := by
    simpa [prefixWord, tailWord_2493973, baseEnd_2493973] using wordTrace_append hprefix tailTrace_2493973
  have hstable : (prefixWord ++ tailWord_2493973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493973).length < 2 ^ (prefixWord ++ tailWord_2493973).sum := by decide
  have hdescent : baseEnd_2493973 < baseStart_2493973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2493980 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_2493980 : Nat := 118140960795 + 2493980 * 2 ^ 59
def prefixEnd_2493980 : Nat := 4983230072969 + 3 ^ 40 * 2493980 * 2
def baseEnd_2493980 : Nat := 1280610482700257525480401

theorem tailTrace_2493980 : CollatzResearch.WordTrace tailWord_2493980 prefixEnd_2493980 1280610482700257525480401 := by
  unfold tailWord_2493980
  simp only [CollatzResearch.WordTrace]
  refine ⟨45481461752371936359231697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60641949003162581812308929 45481461752371936359231697)
  ·
    refine ⟨34111096314278952269423773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45481461752371936359231697 34111096314278952269423773)
    ·
      refine ⟨12791661117854607101033915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34111096314278952269423773 12791661117854607101033915)
      ·
        refine ⟨19187491676781910651550873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12791661117854607101033915 19187491676781910651550873)
        ·
          refine ⟨14390618757586432988663155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19187491676781910651550873 14390618757586432988663155)
          ·
            refine ⟨21585928136379649482994733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14390618757586432988663155 21585928136379649482994733)
            ·
              refine ⟨8094723051142368556123025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21585928136379649482994733 8094723051142368556123025)
              ·
                refine ⟨6071042288356776417092269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8094723051142368556123025 6071042288356776417092269)
                ·
                  refine ⟨2276640858133791156409601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6071042288356776417092269 2276640858133791156409601)
                  ·
                    refine ⟨1707480643600343367307201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276640858133791156409601 1707480643600343367307201)
                    ·
                      refine ⟨1280610482700257525480401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707480643600343367307201 1280610482700257525480401)
                      ·
                        rfl

theorem cell23_2493980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_2493980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2493980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2493980 prefixEnd_2493980 := by exact prefixLift 2493980
  have htrace : WordTrace (prefixWord ++ tailWord_2493980) baseStart_2493980 baseEnd_2493980 := by
    simpa [prefixWord, tailWord_2493980, baseEnd_2493980] using wordTrace_append hprefix tailTrace_2493980
  have hstable : (prefixWord ++ tailWord_2493980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2493980).length < 2 ^ (prefixWord ++ tailWord_2493980).sum := by decide
  have hdescent : baseEnd_2493980 < baseStart_2493980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2493980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494087 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_2494087 : Nat := 118140960795 + 2494087 * 2 ^ 59
def prefixEnd_2494087 : Nat := 4983230072969 + 3 ^ 40 * 2494087 * 2
def baseEnd_2494087 : Nat := 1280665425130288606842409

theorem tailTrace_2494087 : CollatzResearch.WordTrace tailWord_2494087 prefixEnd_2494087 1280665425130288606842409 := by
  unfold tailWord_2494087
  simp only [CollatzResearch.WordTrace]
  refine ⟨90966826115356229992608515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60644550743570819995072343 90966826115356229992608515)
  ·
    refine ⟨136450239173034344988912773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90966826115356229992608515 136450239173034344988912773)
    ·
      refine ⟨25584419844943939685421145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136450239173034344988912773 25584419844943939685421145)
      ·
        refine ⟨19188314883707954764065859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25584419844943939685421145 19188314883707954764065859)
        ·
          refine ⟨28782472325561932146098789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19188314883707954764065859 28782472325561932146098789)
          ·
            refine ⟨5396713561042862277393523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28782472325561932146098789 5396713561042862277393523)
            ·
              refine ⟨8095070341564293416090285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396713561042862277393523 8095070341564293416090285)
              ·
                refine ⟨3035651378086610031033857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8095070341564293416090285 3035651378086610031033857)
                ·
                  refine ⟨2276738533564957523275393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3035651378086610031033857 2276738533564957523275393)
                  ·
                    refine ⟨1707553900173718142456545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2276738533564957523275393 1707553900173718142456545)
                    ·
                      refine ⟨1280665425130288606842409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707553900173718142456545 1280665425130288606842409)
                      ·
                        rfl

theorem cell23_2494087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_2494087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494087 prefixEnd_2494087 := by exact prefixLift 2494087
  have htrace : WordTrace (prefixWord ++ tailWord_2494087) baseStart_2494087 baseEnd_2494087 := by
    simpa [prefixWord, tailWord_2494087, baseEnd_2494087] using wordTrace_append hprefix tailTrace_2494087
  have hstable : (prefixWord ++ tailWord_2494087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494087).length < 2 ^ (prefixWord ++ tailWord_2494087).sum := by decide
  have hdescent : baseEnd_2494087 < baseStart_2494087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494157 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2494157 : Nat := 118140960795 + 2494157 * 2 ^ 59
def prefixEnd_2494157 : Nat := 4983230072969 + 3 ^ 40 * 2494157 * 2
def baseEnd_2494157 : Nat := 426900456258701110989029

theorem tailTrace_2494157 : CollatzResearch.WordTrace tailWord_2494157 prefixEnd_2494157 426900456258701110989029 := by
  unfold tailWord_2494157
  simp only [CollatzResearch.WordTrace]
  refine ⟨90969379225102631947656725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60646252816735087965104483 90969379225102631947656725)
  ·
    refine ⟨4264189651176685872546409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90969379225102631947656725 4264189651176685872546409)
    ·
      refine ⟨3198142238382514404409807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4264189651176685872546409 3198142238382514404409807)
      ·
        refine ⟨4797213357573771606614711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3198142238382514404409807 4797213357573771606614711)
        ·
          refine ⟨7195820036360657409922067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797213357573771606614711 7195820036360657409922067)
          ·
            refine ⟨10793730054540986114883101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7195820036360657409922067 10793730054540986114883101)
            ·
              refine ⟨4047648770452869793081163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10793730054540986114883101 4047648770452869793081163)
              ·
                refine ⟨6071473155679304689621745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047648770452869793081163 6071473155679304689621745)
                ·
                  refine ⟨4553604866759478517216309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6071473155679304689621745 4553604866759478517216309)
                  ·
                    refine ⟨426900456258701110989029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4553604866759478517216309 426900456258701110989029)
                    ·
                      rfl

theorem cell23_2494157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2494157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494157 prefixEnd_2494157 := by exact prefixLift 2494157
  have htrace : WordTrace (prefixWord ++ tailWord_2494157) baseStart_2494157 baseEnd_2494157 := by
    simpa [prefixWord, tailWord_2494157, baseEnd_2494157] using wordTrace_append hprefix tailTrace_2494157
  have hstable : (prefixWord ++ tailWord_2494157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494157).length < 2 ^ (prefixWord ++ tailWord_2494157).sum := by decide
  have hdescent : baseEnd_2494157 < baseStart_2494157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494210 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2494210 : Nat := 118140960795 + 2494210 * 2 ^ 59
def prefixEnd_2494210 : Nat := 4983230072969 + 3 ^ 40 * 2494210 * 2
def baseEnd_2494210 : Nat := 1280728583250791625604343

theorem tailTrace_2494210 : CollatzResearch.WordTrace tailWord_2494210 prefixEnd_2494210 1280728583250791625604343 := by
  unfold tailWord_2494210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22742828073477655499834021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60647541529273747999557389 22742828073477655499834021)
  ·
    refine ⟨4264280263777060406218879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22742828073477655499834021 4264280263777060406218879)
    ·
      refine ⟨6396420395665590609328319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264280263777060406218879 6396420395665590609328319)
      ·
        refine ⟨9594630593498385913992479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6396420395665590609328319 9594630593498385913992479)
        ·
          refine ⟨14391945890247578870988719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9594630593498385913992479 14391945890247578870988719)
          ·
            refine ⟨21587918835371368306483079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14391945890247578870988719 21587918835371368306483079)
            ·
              refine ⟨32381878253057052459724619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21587918835371368306483079 32381878253057052459724619)
              ·
                refine ⟨48572817379585578689586929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32381878253057052459724619 48572817379585578689586929)
                ·
                  refine ⟨36429613034689184017190197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48572817379585578689586929 36429613034689184017190197)
                  ·
                    refine ⟨3415276222002111001611581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36429613034689184017190197 3415276222002111001611581)
                    ·
                      refine ⟨1280728583250791625604343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3415276222002111001611581 1280728583250791625604343)
                      ·
                        rfl

theorem cell23_2494210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2494210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494210 prefixEnd_2494210 := by exact prefixLift 2494210
  have htrace : WordTrace (prefixWord ++ tailWord_2494210) baseStart_2494210 baseEnd_2494210 := by
    simpa [prefixWord, tailWord_2494210, baseEnd_2494210] using wordTrace_append hprefix tailTrace_2494210
  have hstable : (prefixWord ++ tailWord_2494210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494210).length < 2 ^ (prefixWord ++ tailWord_2494210).sum := by decide
  have hdescent : baseEnd_2494210 < baseStart_2494210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494220 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_2494220 : Nat := 118140960795 + 2494220 * 2 ^ 59
def prefixEnd_2494220 : Nat := 4983230072969 + 3 ^ 40 * 2494220 * 2
def baseEnd_2494220 : Nat := 1280733718057336586479297

theorem tailTrace_2494220 : CollatzResearch.WordTrace tailWord_2494220 prefixEnd_2494220 1280733718057336586479297 := by
  unfold tailWord_2494220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45485838511937196853600057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60647784682582929138133409 45485838511937196853600057)
  ·
    refine ⟨34114378883952897640200043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45485838511937196853600057 34114378883952897640200043)
    ·
      refine ⟨51171568325929346460300065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34114378883952897640200043 51171568325929346460300065)
      ·
        refine ⟨38378676244447009845225049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51171568325929346460300065 38378676244447009845225049)
        ·
          refine ⟨28784007183335257383918787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38378676244447009845225049 28784007183335257383918787)
          ·
            refine ⟨43176010775002886075878181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28784007183335257383918787 43176010775002886075878181)
            ·
              refine ⟨8095502020313041139227159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43176010775002886075878181 8095502020313041139227159)
              ·
                refine ⟨12143253030469561708840739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095502020313041139227159 12143253030469561708840739)
                ·
                  refine ⟨18214879545704342563261109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12143253030469561708840739 18214879545704342563261109)
                  ·
                    refine ⟨1707644957409782115305729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18214879545704342563261109 1707644957409782115305729)
                    ·
                      refine ⟨1280733718057336586479297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707644957409782115305729 1280733718057336586479297)
                      ·
                        rfl

theorem cell23_2494220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_2494220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494220 prefixEnd_2494220 := by exact prefixLift 2494220
  have htrace : WordTrace (prefixWord ++ tailWord_2494220) baseStart_2494220 baseEnd_2494220 := by
    simpa [prefixWord, tailWord_2494220, baseEnd_2494220] using wordTrace_append hprefix tailTrace_2494220
  have hstable : (prefixWord ++ tailWord_2494220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494220).length < 2 ^ (prefixWord ++ tailWord_2494220).sum := by decide
  have hdescent : baseEnd_2494220 < baseStart_2494220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494227 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 1, 1, 3]
def baseStart_2494227 : Nat := 118140960795 + 2494227 * 2 ^ 59
def prefixEnd_2494227 : Nat := 4983230072969 + 3 ^ 40 * 2494227 * 2
def baseEnd_2494227 : Nat := 1280737312421918059091765

theorem tailTrace_2494227 : CollatzResearch.WordTrace tailWord_2494227 prefixEnd_2494227 1280737312421918059091765 := by
  unfold tailWord_2494227
  simp only [CollatzResearch.WordTrace]
  refine ⟨90971932334849033902704935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60647954889899355935136623 90971932334849033902704935)
  ·
    refine ⟨136457898502273550854057403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90971932334849033902704935 136457898502273550854057403)
    ·
      refine ⟨204686847753410326281086105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136457898502273550854057403 204686847753410326281086105)
      ·
        refine ⟨153515135815057744710814579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204686847753410326281086105 153515135815057744710814579)
        ·
          refine ⟨230272703722586617066221869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153515135815057744710814579 230272703722586617066221869)
          ·
            refine ⟨86352263895969981399833201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230272703722586617066221869 86352263895969981399833201)
            ·
              refine ⟨64764197921977486049874901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86352263895969981399833201 64764197921977486049874901)
              ·
                refine ⟨1517910888796347329293943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64764197921977486049874901 1517910888796347329293943)
                ·
                  refine ⟨2276866333194520993940915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517910888796347329293943 2276866333194520993940915)
                  ·
                    refine ⟨3415299499791781490911373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2276866333194520993940915 3415299499791781490911373)
                    ·
                      refine ⟨1280737312421918059091765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3415299499791781490911373 1280737312421918059091765)
                      ·
                        rfl

theorem cell23_2494227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 1, 3].length) (baseStart_2494227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494227 prefixEnd_2494227 := by exact prefixLift 2494227
  have htrace : WordTrace (prefixWord ++ tailWord_2494227) baseStart_2494227 baseEnd_2494227 := by
    simpa [prefixWord, tailWord_2494227, baseEnd_2494227] using wordTrace_append hprefix tailTrace_2494227
  have hstable : (prefixWord ++ tailWord_2494227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494227).length < 2 ^ (prefixWord ++ tailWord_2494227).sum := by decide
  have hdescent : baseEnd_2494227 < baseStart_2494227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494238 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2494238 : Nat := 118140960795 + 2494238 * 2 ^ 59
def prefixEnd_2494238 : Nat := 4983230072969 + 3 ^ 40 * 2494238 * 2
def baseEnd_2494238 : Nat := 426914320236372505351405

theorem tailTrace_2494238 : CollatzResearch.WordTrace tailWord_2494238 prefixEnd_2494238 426914320236372505351405 := by
  unfold tailWord_2494238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371541692226147847669421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60648222358539455187570245 11371541692226147847669421)
  ·
    refine ⟨4264328134584805442876033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11371541692226147847669421 4264328134584805442876033)
    ·
      refine ⟨3198246100938604082157025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4264328134584805442876033 3198246100938604082157025)
      ·
        refine ⟨2398684575703953061617769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3198246100938604082157025 2398684575703953061617769)
        ·
          refine ⟨1799013431777964796213327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398684575703953061617769 1799013431777964796213327)
          ·
            refine ⟨2698520147666947194319991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799013431777964796213327 2698520147666947194319991)
            ·
              refine ⟨4047780221500420791479987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698520147666947194319991 4047780221500420791479987)
              ·
                refine ⟨6071670332250631187219981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047780221500420791479987 6071670332250631187219981)
                ·
                  refine ⟨2276876374593986695207493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6071670332250631187219981 2276876374593986695207493)
                  ·
                    refine ⟨426914320236372505351405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2276876374593986695207493 426914320236372505351405)
                    ·
                      rfl

theorem cell23_2494238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2494238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494238 prefixEnd_2494238 := by exact prefixLift 2494238
  have htrace : WordTrace (prefixWord ++ tailWord_2494238) baseStart_2494238 baseEnd_2494238 := by
    simpa [prefixWord, tailWord_2494238, baseEnd_2494238] using wordTrace_append hprefix tailTrace_2494238
  have hstable : (prefixWord ++ tailWord_2494238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494238).length < 2 ^ (prefixWord ++ tailWord_2494238).sum := by decide
  have hdescent : baseEnd_2494238 < baseStart_2494238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494244 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2494244 : Nat := 118140960795 + 2494244 * 2 ^ 59
def prefixEnd_2494244 : Nat := 4983230072969 + 3 ^ 40 * 2494244 * 2
def baseEnd_2494244 : Nat := 1280746041593044492579187

theorem tailTrace_2494244 : CollatzResearch.WordTrace tailWord_2494244 prefixEnd_2494244 1280746041593044492579187 := by
  unfold tailWord_2494244
  simp only [CollatzResearch.WordTrace]
  refine ⟨45486276187893722903036893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60648368250524963870715857 45486276187893722903036893)
  ·
    refine ⟨17057353570460146088638835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45486276187893722903036893 17057353570460146088638835)
    ·
      refine ⟨25586030355690219132958253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17057353570460146088638835 25586030355690219132958253)
      ·
        refine ⟨9594761383383832174859345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25586030355690219132958253 9594761383383832174859345)
        ·
          refine ⟨7196071037537874131144509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9594761383383832174859345 7196071037537874131144509)
          ·
            refine ⟨2698526639076702799179191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7196071037537874131144509 2698526639076702799179191)
            ·
              refine ⟨4047789958615054198768787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698526639076702799179191 4047789958615054198768787)
              ·
                refine ⟨6071684937922581298153181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047789958615054198768787 6071684937922581298153181)
                ·
                  refine ⟨2276881851720967986807443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6071684937922581298153181 2276881851720967986807443)
                  ·
                    refine ⟨3415322777581451980211165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2276881851720967986807443 3415322777581451980211165)
                    ·
                      refine ⟨1280746041593044492579187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3415322777581451980211165 1280746041593044492579187)
                      ·
                        rfl

theorem cell23_2494244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2494244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494244 prefixEnd_2494244 := by exact prefixLift 2494244
  have htrace : WordTrace (prefixWord ++ tailWord_2494244) baseStart_2494244 baseEnd_2494244 := by
    simpa [prefixWord, tailWord_2494244, baseEnd_2494244] using wordTrace_append hprefix tailTrace_2494244
  have hstable : (prefixWord ++ tailWord_2494244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494244).length < 2 ^ (prefixWord ++ tailWord_2494244).sum := by decide
  have hdescent : baseEnd_2494244 < baseStart_2494244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494280 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2494280 : Nat := 118140960795 + 2494280 * 2 ^ 59
def prefixEnd_2494280 : Nat := 4983230072969 + 3 ^ 40 * 2494280 * 2
def baseEnd_2494280 : Nat := 1280764526896606351729021

theorem tailTrace_2494280 : CollatzResearch.WordTrace tailWord_2494280 prefixEnd_2494280 1280764526896606351729021 := by
  unfold tailWord_2494280
  simp only [CollatzResearch.WordTrace]
  refine ⟨45486932701828511977192147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60649243602438015969589529 45486932701828511977192147)
  ·
    refine ⟨68230399052742767965788221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45486932701828511977192147 68230399052742767965788221)
    ·
      refine ⟨25586399644778537987170583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68230399052742767965788221 25586399644778537987170583)
      ·
        refine ⟨38379599467167806980755875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25586399644778537987170583 38379599467167806980755875)
        ·
          refine ⟨57569399200751710471133813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38379599467167806980755875 57569399200751710471133813)
          ·
            refine ⟨5397131175070472856668795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57569399200751710471133813 5397131175070472856668795)
            ·
              refine ⟨8095696762605709285003193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397131175070472856668795 8095696762605709285003193)
              ·
                refine ⟨6071772571954281963752395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8095696762605709285003193 6071772571954281963752395)
                ·
                  refine ⟨9107658857931422945628593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071772571954281963752395 9107658857931422945628593)
                  ·
                    refine ⟨6830744143448567209221445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9107658857931422945628593 6830744143448567209221445)
                    ·
                      refine ⟨1280764526896606351729021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6830744143448567209221445 1280764526896606351729021)
                      ·
                        rfl

theorem cell23_2494280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2494280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494280 prefixEnd_2494280 := by exact prefixLift 2494280
  have htrace : WordTrace (prefixWord ++ tailWord_2494280) baseStart_2494280 baseEnd_2494280 := by
    simpa [prefixWord, tailWord_2494280, baseEnd_2494280] using wordTrace_append hprefix tailTrace_2494280
  have hstable : (prefixWord ++ tailWord_2494280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494280).length < 2 ^ (prefixWord ++ tailWord_2494280).sum := by decide
  have hdescent : baseEnd_2494280 < baseStart_2494280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494284 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2494284 : Nat := 118140960795 + 2494284 * 2 ^ 59
def prefixEnd_2494284 : Nat := 4983230072969 + 3 ^ 40 * 2494284 * 2
def baseEnd_2494284 : Nat := 1280766580819224336079003

theorem tailTrace_2494284 : CollatzResearch.WordTrace tailWord_2494284 prefixEnd_2494284 1280766580819224336079003 := by
  unfold tailWord_2494284
  simp only [CollatzResearch.WordTrace]
  refine ⟨45487005647821266318764953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60649340863761688425019937 45487005647821266318764953)
  ·
    refine ⟨34115254235865949739073715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45487005647821266318764953 34115254235865949739073715)
    ·
      refine ⟨51172881353798924608610573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34115254235865949739073715 51172881353798924608610573)
      ·
        refine ⟨19189830507674596728228965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51172881353798924608610573 19189830507674596728228965)
        ·
          refine ⟨3598093220188986886542931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19189830507674596728228965 3598093220188986886542931)
          ·
            refine ⟨5397139830283480329814397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598093220188986886542931 5397139830283480329814397)
            ·
              refine ⟨2023927436356305123680399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5397139830283480329814397 2023927436356305123680399)
              ·
                refine ⟨3035891154534457685520599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023927436356305123680399 3035891154534457685520599)
                ·
                  refine ⟨4553836731801686528280899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035891154534457685520599 4553836731801686528280899)
                  ·
                    refine ⟨6830755097702529792421349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553836731801686528280899 6830755097702529792421349)
                    ·
                      refine ⟨1280766580819224336079003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6830755097702529792421349 1280766580819224336079003)
                      ·
                        rfl

theorem cell23_2494284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2494284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494284 prefixEnd_2494284 := by exact prefixLift 2494284
  have htrace : WordTrace (prefixWord ++ tailWord_2494284) baseStart_2494284 baseEnd_2494284 := by
    simpa [prefixWord, tailWord_2494284, baseEnd_2494284] using wordTrace_append hprefix tailTrace_2494284
  have hstable : (prefixWord ++ tailWord_2494284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494284).length < 2 ^ (prefixWord ++ tailWord_2494284).sum := by decide
  have hdescent : baseEnd_2494284 < baseStart_2494284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494303 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 7]
def baseStart_2494303 : Nat := 118140960795 + 2494303 * 2 ^ 59
def prefixEnd_2494303 : Nat := 4983230072969 + 3 ^ 40 * 2494303 * 2
def baseEnd_2494303 : Nat := 426925445650553253913805

theorem tailTrace_2494303 : CollatzResearch.WordTrace tailWord_2494303 prefixEnd_2494303 426925445650553253913805 := by
  unfold tailWord_2494303
  simp only [CollatzResearch.WordTrace]
  refine ⟨90974704282573698882471563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60649802855049132588314375 90974704282573698882471563)
  ·
    refine ⟨136462056423860548323707345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90974704282573698882471563 136462056423860548323707345)
    ·
      refine ⟨102346542317895411242780509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136462056423860548323707345 102346542317895411242780509)
      ·
        refine ⟨38379953369210779216042691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102346542317895411242780509 38379953369210779216042691)
        ·
          refine ⟨57569930053816168824064037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38379953369210779216042691 57569930053816168824064037)
          ·
            refine ⟨10794361885090531654512007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57569930053816168824064037 10794361885090531654512007)
            ·
              refine ⟨16191542827635797481768011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10794361885090531654512007 16191542827635797481768011)
              ·
                refine ⟨24287314241453696222652017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16191542827635797481768011 24287314241453696222652017)
                ·
                  refine ⟨18215485681090272166989013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24287314241453696222652017 18215485681090272166989013)
                  ·
                    refine ⟨426925445650553253913805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18215485681090272166989013 426925445650553253913805)
                    ·
                      rfl

theorem cell23_2494303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_2494303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494303 prefixEnd_2494303 := by exact prefixLift 2494303
  have htrace : WordTrace (prefixWord ++ tailWord_2494303) baseStart_2494303 baseEnd_2494303 := by
    simpa [prefixWord, tailWord_2494303, baseEnd_2494303] using wordTrace_append hprefix tailTrace_2494303
  have hstable : (prefixWord ++ tailWord_2494303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494303).length < 2 ^ (prefixWord ++ tailWord_2494303).sum := by decide
  have hdescent : baseEnd_2494303 < baseStart_2494303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494307 : List Nat := [1, 1, 1, 5, 5, 1, 1, 8]
def baseStart_2494307 : Nat := 118140960795 + 2494307 * 2 ^ 59
def prefixEnd_2494307 : Nat := 4983230072969 + 3 ^ 40 * 2494307 * 2
def baseEnd_2494307 : Nat := 47436236699047323929311

theorem tailTrace_2494307 : CollatzResearch.WordTrace tailWord_2494307 prefixEnd_2494307 47436236699047323929311 := by
  unfold tailWord_2494307
  simp only [CollatzResearch.WordTrace]
  refine ⟨90974850174559207565617175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60649900116372805043744783 90974850174559207565617175)
  ·
    refine ⟨136462275261838811348425763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90974850174559207565617175 136462275261838811348425763)
    ·
      refine ⟨204693412892758217022638645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136462275261838811348425763 204693412892758217022638645)
      ·
        refine ⟨19190007458696082845872373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204693412892758217022638645 19190007458696082845872373)
        ·
          refine ⟨1799063199252757766800535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19190007458696082845872373 1799063199252757766800535)
          ·
            refine ⟨2698594798879136650200803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799063199252757766800535 2698594798879136650200803)
            ·
              refine ⟨4047892198318704975301205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698594798879136650200803 4047892198318704975301205)
              ·
                refine ⟨47436236699047323929311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4047892198318704975301205 47436236699047323929311)
                ·
                  rfl

theorem cell23_2494307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 8].length) (baseStart_2494307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494307 prefixEnd_2494307 := by exact prefixLift 2494307
  have htrace : WordTrace (prefixWord ++ tailWord_2494307) baseStart_2494307 baseEnd_2494307 := by
    simpa [prefixWord, tailWord_2494307, baseEnd_2494307] using wordTrace_append hprefix tailTrace_2494307
  have hstable : (prefixWord ++ tailWord_2494307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494307).length < 2 ^ (prefixWord ++ tailWord_2494307).sum := by decide
  have hdescent : baseEnd_2494307 < baseStart_2494307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494314 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2494314 : Nat := 118140960795 + 2494314 * 2 ^ 59
def prefixEnd_2494314 : Nat := 4983230072969 + 3 ^ 40 * 2494314 * 2
def baseEnd_2494314 : Nat := 1280781985238859218703865

theorem tailTrace_2494314 : CollatzResearch.WordTrace tailWord_2494314 prefixEnd_2494314 1280781985238859218703865 := by
  unfold tailWord_2494314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22743776371383461940280499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60650070323689231840747997 22743776371383461940280499)
  ·
    refine ⟨34115664557075192910420749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22743776371383461940280499 34115664557075192910420749)
    ·
      refine ⟨12793374208903197341407781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34115664557075192910420749 12793374208903197341407781)
      ·
        refine ⟨2398757664169349501513959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12793374208903197341407781 2398757664169349501513959)
        ·
          refine ⟨3598136496254024252270939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398757664169349501513959 3598136496254024252270939)
          ·
            refine ⟨5397204744381036378406409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598136496254024252270939 5397204744381036378406409)
            ·
              refine ⟨4047903558285777283804807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5397204744381036378406409 4047903558285777283804807)
              ·
                refine ⟨6071855337428665925707211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047903558285777283804807 6071855337428665925707211)
                ·
                  refine ⟨9107783006142998888560817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071855337428665925707211 9107783006142998888560817)
                  ·
                    refine ⟨6830837254607249166420613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9107783006142998888560817 6830837254607249166420613)
                    ·
                      refine ⟨1280781985238859218703865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6830837254607249166420613 1280781985238859218703865)
                      ·
                        rfl

theorem cell23_2494314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2494314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494314 prefixEnd_2494314 := by exact prefixLift 2494314
  have htrace : WordTrace (prefixWord ++ tailWord_2494314) baseStart_2494314 baseEnd_2494314 := by
    simpa [prefixWord, tailWord_2494314, baseEnd_2494314] using wordTrace_append hprefix tailTrace_2494314
  have hstable : (prefixWord ++ tailWord_2494314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494314).length < 2 ^ (prefixWord ++ tailWord_2494314).sum := by decide
  have hdescent : baseEnd_2494314 < baseStart_2494314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494323 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_2494323 : Nat := 118140960795 + 2494323 * 2 ^ 59
def prefixEnd_2494323 : Nat := 4983230072969 + 3 ^ 40 * 2494323 * 2
def baseEnd_2494323 : Nat := 1280786606564749683491323

theorem tailTrace_2494323 : CollatzResearch.WordTrace tailWord_2494323 prefixEnd_2494323 1280786606564749683491323 := by
  unfold tailWord_2494323
  simp only [CollatzResearch.WordTrace]
  refine ⟨90975433742501242298199623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60650289161667494865466415 90975433742501242298199623)
  ·
    refine ⟨136463150613751863447299435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90975433742501242298199623 136463150613751863447299435)
    ·
      refine ⟨204694725920627795170949153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136463150613751863447299435 204694725920627795170949153)
      ·
        refine ⟨153521044440470846378211865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204694725920627795170949153 153521044440470846378211865)
        ·
          refine ⟨115140783330353134783658899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153521044440470846378211865 115140783330353134783658899)
          ·
            refine ⟨172711174995529702175488349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115140783330353134783658899 172711174995529702175488349)
            ·
              refine ⟨64766690623323638315808131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172711174995529702175488349 64766690623323638315808131)
              ·
                refine ⟨97150035934985457473712197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64766690623323638315808131 97150035934985457473712197)
                ·
                  refine ⟨18215631737809773276321037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97150035934985457473712197 18215631737809773276321037)
                  ·
                    refine ⟨6830861901678664978620389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18215631737809773276321037 6830861901678664978620389)
                    ·
                      refine ⟨1280786606564749683491323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6830861901678664978620389 1280786606564749683491323)
                      ·
                        rfl

theorem cell23_2494323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_2494323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494323 prefixEnd_2494323 := by exact prefixLift 2494323
  have htrace : WordTrace (prefixWord ++ tailWord_2494323) baseStart_2494323 baseEnd_2494323 := by
    simpa [prefixWord, tailWord_2494323, baseEnd_2494323] using wordTrace_append hprefix tailTrace_2494323
  have hstable : (prefixWord ++ tailWord_2494323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494323).length < 2 ^ (prefixWord ++ tailWord_2494323).sum := by decide
  have hdescent : baseEnd_2494323 < baseStart_2494323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494333 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2494333 : Nat := 118140960795 + 2494333 * 2 ^ 59
def prefixEnd_2494333 : Nat := 4983230072969 + 3 ^ 40 * 2494333 * 2
def baseEnd_2494333 : Nat := 426930580457098214788759

theorem tailTrace_2494333 : CollatzResearch.WordTrace tailWord_2494333 prefixEnd_2494333 426930580457098214788759 := by
  unfold tailWord_2494333
  simp only [CollatzResearch.WordTrace]
  refine ⟨90975798472465014006063653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60650532314976676004042435 90975798472465014006063653)
  ·
    refine ⟨17057962213587190126136935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90975798472465014006063653 17057962213587190126136935)
    ·
      refine ⟨25586943320380785189205403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17057962213587190126136935 25586943320380785189205403)
      ·
        refine ⟨38380414980571177783808105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25586943320380785189205403 38380414980571177783808105)
        ·
          refine ⟨28785311235428383337856079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38380414980571177783808105 28785311235428383337856079)
          ·
            refine ⟨43177966853142575006784119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28785311235428383337856079 43177966853142575006784119)
            ·
              refine ⟨64766950279713862510176179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43177966853142575006784119 64766950279713862510176179)
              ·
                refine ⟨97150425419570793765264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64766950279713862510176179 97150425419570793765264269)
                ·
                  refine ⟨36431409532339047661974101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97150425419570793765264269 36431409532339047661974101)
                  ·
                    refine ⟨426930580457098214788759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36431409532339047661974101 426930580457098214788759)
                    ·
                      rfl

theorem cell23_2494333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2494333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494333 prefixEnd_2494333 := by exact prefixLift 2494333
  have htrace : WordTrace (prefixWord ++ tailWord_2494333) baseStart_2494333 baseEnd_2494333 := by
    simpa [prefixWord, tailWord_2494333, baseEnd_2494333] using wordTrace_append hprefix tailTrace_2494333
  have hstable : (prefixWord ++ tailWord_2494333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494333).length < 2 ^ (prefixWord ++ tailWord_2494333).sum := by decide
  have hdescent : baseEnd_2494333 < baseStart_2494333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494334 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2494334 : Nat := 118140960795 + 2494334 * 2 ^ 59
def prefixEnd_2494334 : Nat := 4983230072969 + 3 ^ 40 * 2494334 * 2
def baseEnd_2494334 : Nat := 1280792254851949140453773

theorem tailTrace_2494334 : CollatzResearch.WordTrace tailWord_2494334 prefixEnd_2494334 1280792254851949140453773 := by
  unfold tailWord_2494334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371979368182673897106257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60650556630307594117900037 11371979368182673897106257)
  ·
    refine ⟨8528984526137005422829693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11371979368182673897106257 8528984526137005422829693)
    ·
      refine ⟨3198369197301377033561135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8528984526137005422829693 3198369197301377033561135)
      ·
        refine ⟨4797553795952065550341703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3198369197301377033561135 4797553795952065550341703)
        ·
          refine ⟨7196330693928098325512555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797553795952065550341703 7196330693928098325512555)
          ·
            refine ⟨10794496040892147488268833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7196330693928098325512555 10794496040892147488268833)
            ·
              refine ⟨8095872030669110616201625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10794496040892147488268833 8095872030669110616201625)
              ·
                refine ⟨6071904023001832962151219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8095872030669110616201625 6071904023001832962151219)
                ·
                  refine ⟨9107856034502749443226829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071904023001832962151219 9107856034502749443226829)
                  ·
                    refine ⟨3415446012938531041210061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9107856034502749443226829 3415446012938531041210061)
                    ·
                      refine ⟨1280792254851949140453773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3415446012938531041210061 1280792254851949140453773)
                      ·
                        rfl

theorem cell23_2494334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2494334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494334 prefixEnd_2494334 := by exact prefixLift 2494334
  have htrace : WordTrace (prefixWord ++ tailWord_2494334) baseStart_2494334 baseEnd_2494334 := by
    simpa [prefixWord, tailWord_2494334, baseEnd_2494334] using wordTrace_append hprefix tailTrace_2494334
  have hstable : (prefixWord ++ tailWord_2494334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494334).length < 2 ^ (prefixWord ++ tailWord_2494334).sum := by decide
  have hdescent : baseEnd_2494334 < baseStart_2494334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494373 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2494373 : Nat := 118140960795 + 2494373 * 2 ^ 59
def prefixEnd_2494373 : Nat := 4983230072969 + 3 ^ 40 * 2494373 * 2
def baseEnd_2494373 : Nat := 1280812280597474487866093

theorem tailTrace_2494373 : CollatzResearch.WordTrace tailWord_2494373 prefixEnd_2494373 1280812280597474487866093 := by
  unfold tailWord_2494373
  simp only [CollatzResearch.WordTrace]
  refine ⟨90977257392320100837519773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60651504928213400558346515 90977257392320100837519773)
  ·
    refine ⟨34116471522120037814069915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90977257392320100837519773 34116471522120037814069915)
    ·
      refine ⟨51174707283180056721104873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34116471522120037814069915 51174707283180056721104873)
      ·
        refine ⟨38381030462385042540828655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51174707283180056721104873 38381030462385042540828655)
        ·
          refine ⟨57571545693577563811242983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38381030462385042540828655 57571545693577563811242983)
          ·
            refine ⟨86357318540366345716864475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57571545693577563811242983 86357318540366345716864475)
            ·
              refine ⟨129535977810549518575296713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86357318540366345716864475 129535977810549518575296713)
              ·
                refine ⟨97151983357912138931472535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129535977810549518575296713 97151983357912138931472535)
                ·
                  refine ⟨145727975036868208397208803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97151983357912138931472535 145727975036868208397208803)
                  ·
                    refine ⟨218591962555302312595813205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145727975036868208397208803 218591962555302312595813205)
                    ·
                      refine ⟨1280812280597474487866093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 218591962555302312595813205 1280812280597474487866093)
                      ·
                        rfl

theorem cell23_2494373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2494373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494373 prefixEnd_2494373 := by exact prefixLift 2494373
  have htrace : WordTrace (prefixWord ++ tailWord_2494373) baseStart_2494373 baseEnd_2494373 := by
    simpa [prefixWord, tailWord_2494373, baseEnd_2494373] using wordTrace_append hprefix tailTrace_2494373
  have hstable : (prefixWord ++ tailWord_2494373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494373).length < 2 ^ (prefixWord ++ tailWord_2494373).sum := by decide
  have hdescent : baseEnd_2494373 < baseStart_2494373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494410 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_2494410 : Nat := 118140960795 + 2494410 * 2 ^ 59
def prefixEnd_2494410 : Nat := 4983230072969 + 3 ^ 40 * 2494410 * 2
def baseEnd_2494410 : Nat := 426943759793896947701141

theorem tailTrace_2494410 : CollatzResearch.WordTrace tailWord_2494410 prefixEnd_2494410 426943759793896947701141 := by
  unfold tailWord_2494410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22744651723296514039154171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60652404595457370771077789 22744651723296514039154171)
  ·
    refine ⟨34116977584944771058731257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22744651723296514039154171 34116977584944771058731257)
    ·
      refine ⟨25587733188708578294048443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34116977584944771058731257 25587733188708578294048443)
      ·
        refine ⟨38381599783062867441072665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25587733188708578294048443 38381599783062867441072665)
        ·
          refine ⟨28786199837297150580804499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38381599783062867441072665 28786199837297150580804499)
          ·
            refine ⟨43179299755945725871206749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786199837297150580804499 43179299755945725871206749)
            ·
              refine ⟨16192237408479647201702531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43179299755945725871206749 16192237408479647201702531)
              ·
                refine ⟨24288356112719470802553797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16192237408479647201702531 24288356112719470802553797)
                ·
                  refine ⟨4554066771134900775478837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24288356112719470802553797 4554066771134900775478837)
                  ·
                    refine ⟨426943759793896947701141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4554066771134900775478837 426943759793896947701141)
                    ·
                      rfl

theorem cell23_2494410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_2494410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494410 prefixEnd_2494410 := by exact prefixLift 2494410
  have htrace : WordTrace (prefixWord ++ tailWord_2494410) baseStart_2494410 baseEnd_2494410 := by
    simpa [prefixWord, tailWord_2494410, baseEnd_2494410] using wordTrace_append hprefix tailTrace_2494410
  have hstable : (prefixWord ++ tailWord_2494410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494410).length < 2 ^ (prefixWord ++ tailWord_2494410).sum := by decide
  have hdescent : baseEnd_2494410 < baseStart_2494410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494414 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_2494414 : Nat := 118140960795 + 2494414 * 2 ^ 59
def prefixEnd_2494414 : Nat := 4983230072969 + 3 ^ 40 * 2494414 * 2
def baseEnd_2494414 : Nat := 142314814811589869717045

theorem tailTrace_2494414 : CollatzResearch.WordTrace tailWord_2494414 prefixEnd_2494414 142314814811589869717045 := by
  unfold tailWord_2494414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11372344098146445604970287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60652501856781043226508197 11372344098146445604970287)
  ·
    refine ⟨17058516147219668407455431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11372344098146445604970287 17058516147219668407455431)
    ·
      refine ⟨25587774220829502611183147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17058516147219668407455431 25587774220829502611183147)
      ·
        refine ⟨38381661331244253916774721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25587774220829502611183147 38381661331244253916774721)
        ·
          refine ⟨28786245998433190437581041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38381661331244253916774721 28786245998433190437581041)
          ·
            refine ⟨21589684498824892828185781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28786245998433190437581041 21589684498824892828185781)
            ·
              refine ⟨2024032921764833702642417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21589684498824892828185781 2024032921764833702642417)
              ·
                refine ⟨1518024691323625276981813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024032921764833702642417 1518024691323625276981813)
                ·
                  refine ⟨142314814811589869717045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1518024691323625276981813 142314814811589869717045)
                  ·
                    rfl

theorem cell23_2494414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_2494414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494414 prefixEnd_2494414 := by exact prefixLift 2494414
  have htrace : WordTrace (prefixWord ++ tailWord_2494414) baseStart_2494414 baseEnd_2494414 := by
    simpa [prefixWord, tailWord_2494414, baseEnd_2494414] using wordTrace_append hprefix tailTrace_2494414
  have hstable : (prefixWord ++ tailWord_2494414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494414).length < 2 ^ (prefixWord ++ tailWord_2494414).sum := by decide
  have hdescent : baseEnd_2494414 < baseStart_2494414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494425 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 2, 2, 2]
def baseStart_2494425 : Nat := 118140960795 + 2494425 * 2 ^ 59
def prefixEnd_2494425 : Nat := 4983230072969 + 3 ^ 40 * 2494425 * 2
def baseEnd_2494425 : Nat := 1280838981591508284415855

theorem tailTrace_2494425 : CollatzResearch.WordTrace tailWord_2494425 prefixEnd_2494425 1280838981591508284415855 := by
  unfold tailWord_2494425
  simp only [CollatzResearch.WordTrace]
  refine ⟨90979153988131713718412729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60652769325421142478941819 90979153988131713718412729)
  ·
    refine ⟨68234365491098785288809547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90979153988131713718412729 68234365491098785288809547)
    ·
      refine ⟨102351548236648177933214321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68234365491098785288809547 102351548236648177933214321)
      ·
        refine ⟨76763661177486133449910741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102351548236648177933214321 76763661177486133449910741)
        ·
          refine ⟨1799148308847331252732283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76763661177486133449910741 1799148308847331252732283)
          ·
            refine ⟨2698722463270996879098425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799148308847331252732283 2698722463270996879098425)
            ·
              refine ⟨2024041847453247659323819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698722463270996879098425 2024041847453247659323819)
              ·
                refine ⟨3036062771179871488985729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024041847453247659323819 3036062771179871488985729)
                ·
                  refine ⟨2277047078384903616739297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036062771179871488985729 2277047078384903616739297)
                  ·
                    refine ⟨1707785308788677712554473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277047078384903616739297 1707785308788677712554473)
                    ·
                      refine ⟨1280838981591508284415855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707785308788677712554473 1280838981591508284415855)
                      ·
                        rfl

theorem cell23_2494425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_2494425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494425 prefixEnd_2494425 := by exact prefixLift 2494425
  have htrace : WordTrace (prefixWord ++ tailWord_2494425) baseStart_2494425 baseEnd_2494425 := by
    simpa [prefixWord, tailWord_2494425, baseEnd_2494425] using wordTrace_append hprefix tailTrace_2494425
  have hstable : (prefixWord ++ tailWord_2494425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494425).length < 2 ^ (prefixWord ++ tailWord_2494425).sum := by decide
  have hdescent : baseEnd_2494425 < baseStart_2494425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494447 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_2494447 : Nat := 118140960795 + 2494447 * 2 ^ 59
def prefixEnd_2494447 : Nat := 4983230072969 + 3 ^ 40 * 2494447 * 2
def baseEnd_2494447 : Nat := 1280850278165907198340753

theorem tailTrace_2494447 : CollatzResearch.WordTrace tailWord_2494447 prefixEnd_2494447 1280850278165907198340753 := by
  unfold tailWord_2494447
  simp only [CollatzResearch.WordTrace]
  refine ⟨90979956394052011475713595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60653304262701340983809063 90979956394052011475713595)
  ·
    refine ⟨136469934591078017213570393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90979956394052011475713595 136469934591078017213570393)
    ·
      refine ⟨102352450943308512910177795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136469934591078017213570393 102352450943308512910177795)
      ·
        refine ⟨153528676414962769365266693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102352450943308512910177795 153528676414962769365266693)
        ·
          refine ⟨28786626827805519255987505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153528676414962769365266693 28786626827805519255987505)
          ·
            refine ⟨21589970120854139441990629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28786626827805519255987505 21589970120854139441990629)
            ·
              refine ⟨4048119397660151145373243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21589970120854139441990629 4048119397660151145373243)
              ·
                refine ⟨6072179096490226718059865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048119397660151145373243 6072179096490226718059865)
                ·
                  refine ⟨4554134322367670038544899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6072179096490226718059865 4554134322367670038544899)
                  ·
                    refine ⟨6831201483551505057817349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554134322367670038544899 6831201483551505057817349)
                    ·
                      refine ⟨1280850278165907198340753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6831201483551505057817349 1280850278165907198340753)
                      ·
                        rfl

theorem cell23_2494447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_2494447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494447 prefixEnd_2494447 := by exact prefixLift 2494447
  have htrace : WordTrace (prefixWord ++ tailWord_2494447) baseStart_2494447 baseEnd_2494447 := by
    simpa [prefixWord, tailWord_2494447, baseEnd_2494447] using wordTrace_append hprefix tailTrace_2494447
  have hstable : (prefixWord ++ tailWord_2494447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494447).length < 2 ^ (prefixWord ++ tailWord_2494447).sum := by decide
  have hdescent : baseEnd_2494447 < baseStart_2494447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494460 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2494460 : Nat := 118140960795 + 2494460 * 2 ^ 59
def prefixEnd_2494460 : Nat := 4983230072969 + 3 ^ 40 * 2494460 * 2
def baseEnd_2494460 : Nat := 1280856953414415647478193

theorem tailTrace_2494460 : CollatzResearch.WordTrace tailWord_2494460 prefixEnd_2494460 1280856953414415647478193 := by
  unfold tailWord_2494460
  simp only [CollatzResearch.WordTrace]
  refine ⟨45490215271502457347968417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60653620362003276463957889 45490215271502457347968417)
  ·
    refine ⟨34117661453626843010976313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45490215271502457347968417 34117661453626843010976313)
    ·
      refine ⟨25588246090220132258232235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34117661453626843010976313 25588246090220132258232235)
      ·
        refine ⟨38382369135330198387348353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25588246090220132258232235 38382369135330198387348353)
        ·
          refine ⟨28786776851497648790511265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38382369135330198387348353 28786776851497648790511265)
          ·
            refine ⟨21590082638623236592883449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28786776851497648790511265 21590082638623236592883449)
            ·
              refine ⟨16192561978967427444662587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21590082638623236592883449 16192561978967427444662587)
              ·
                refine ⟨24288842968451141166993881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16192561978967427444662587 24288842968451141166993881)
                ·
                  refine ⟨18216632226338355875245411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24288842968451141166993881 18216632226338355875245411)
                  ·
                    refine ⟨27324948339507533812868117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18216632226338355875245411 27324948339507533812868117)
                    ·
                      refine ⟨1280856953414415647478193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27324948339507533812868117 1280856953414415647478193)
                      ·
                        rfl

theorem cell23_2494460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2494460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494460 prefixEnd_2494460 := by exact prefixLift 2494460
  have htrace : WordTrace (prefixWord ++ tailWord_2494460) baseStart_2494460 baseEnd_2494460 := by
    simpa [prefixWord, tailWord_2494460, baseEnd_2494460] using wordTrace_append hprefix tailTrace_2494460
  have hstable : (prefixWord ++ tailWord_2494460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494460).length < 2 ^ (prefixWord ++ tailWord_2494460).sum := by decide
  have hdescent : baseEnd_2494460 < baseStart_2494460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494521 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 6]
def baseStart_2494521 : Nat := 118140960795 + 2494521 * 2 ^ 59
def prefixEnd_2494521 : Nat := 4983230072969 + 3 ^ 40 * 2494521 * 2
def baseEnd_2494521 : Nat := 142320919526037767646157

theorem tailTrace_2494521 : CollatzResearch.WordTrace tailWord_2494521 prefixEnd_2494521 142320919526037767646157 := by
  unfold tailWord_2494521
  simp only [CollatzResearch.WordTrace]
  refine ⟨90982655395783922113907417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60655103597189281409271611 90982655395783922113907417)
  ·
    refine ⟨68236991546837941585430563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90982655395783922113907417 68236991546837941585430563)
    ·
      refine ⟨102355487320256912378145845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68236991546837941585430563 102355487320256912378145845)
      ·
        refine ⟨9595826936274085535451173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102355487320256912378145845 9595826936274085535451173)
        ·
          refine ⟨1799217550551391037897095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9595826936274085535451173 1799217550551391037897095)
          ·
            refine ⟨2698826325827086556845643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799217550551391037897095 2698826325827086556845643)
            ·
              refine ⟨4048239488740629835268465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698826325827086556845643 4048239488740629835268465)
              ·
                refine ⟨3036179616555472376451349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048239488740629835268465 3036179616555472376451349)
                ·
                  refine ⟨142320919526037767646157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3036179616555472376451349 142320919526037767646157)
                  ·
                    rfl

theorem cell23_2494521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 6].length) (baseStart_2494521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494521 prefixEnd_2494521 := by exact prefixLift 2494521
  have htrace : WordTrace (prefixWord ++ tailWord_2494521) baseStart_2494521 baseEnd_2494521 := by
    simpa [prefixWord, tailWord_2494521, baseEnd_2494521] using wordTrace_append hprefix tailTrace_2494521
  have hstable : (prefixWord ++ tailWord_2494521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494521).length < 2 ^ (prefixWord ++ tailWord_2494521).sum := by decide
  have hdescent : baseEnd_2494521 < baseStart_2494521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494524 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_2494524 : Nat := 118140960795 + 2494524 * 2 ^ 59
def prefixEnd_2494524 : Nat := 4983230072969 + 3 ^ 40 * 2494524 * 2
def baseEnd_2494524 : Nat := 1280889816176303397077899

theorem tailTrace_2494524 : CollatzResearch.WordTrace tailWord_2494524 prefixEnd_2494524 1280889816176303397077899 := by
  unfold tailWord_2494524
  simp only [CollatzResearch.WordTrace]
  refine ⟨45491382407386526813133313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60655176543182035750844417 45491382407386526813133313)
  ·
    refine ⟨34118536805539895109849985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45491382407386526813133313 34118536805539895109849985)
    ·
      refine ⟨25588902604154921332387489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34118536805539895109849985 25588902604154921332387489)
      ·
        refine ⟨19191676953116190999290617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25588902604154921332387489 19191676953116190999290617)
        ·
          refine ⟨14393757714837143249467963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19191676953116190999290617 14393757714837143249467963)
          ·
            refine ⟨21590636572255714874201945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14393757714837143249467963 21590636572255714874201945)
            ·
              refine ⟨16192977429191786155651459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21590636572255714874201945 16192977429191786155651459)
              ·
                refine ⟨24289466143787679233477189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16192977429191786155651459 24289466143787679233477189)
                ·
                  refine ⟨4554274901960189856276973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24289466143787679233477189 4554274901960189856276973)
                  ·
                    refine ⟨1707853088235071196103865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4554274901960189856276973 1707853088235071196103865)
                    ·
                      refine ⟨1280889816176303397077899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707853088235071196103865 1280889816176303397077899)
                      ·
                        rfl

theorem cell23_2494524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_2494524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494524 prefixEnd_2494524 := by exact prefixLift 2494524
  have htrace : WordTrace (prefixWord ++ tailWord_2494524) baseStart_2494524 baseEnd_2494524 := by
    simpa [prefixWord, tailWord_2494524, baseEnd_2494524] using wordTrace_append hprefix tailTrace_2494524
  have hstable : (prefixWord ++ tailWord_2494524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494524).length < 2 ^ (prefixWord ++ tailWord_2494524).sum := by decide
  have hdescent : baseEnd_2494524 < baseStart_2494524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494554 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_2494554 : Nat := 118140960795 + 2494554 * 2 ^ 59
def prefixEnd_2494554 : Nat := 4983230072969 + 3 ^ 40 * 2494554 * 2
def baseEnd_2494554 : Nat := 1280905220595938279702761

theorem tailTrace_2494554 : CollatzResearch.WordTrace tailWord_2494554 prefixEnd_2494554 1280905220595938279702761 := by
  unfold tailWord_2494554
  simp only [CollatzResearch.WordTrace]
  refine ⟨22745964751166092187464679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60655906003109579166572477 22745964751166092187464679)
  ·
    refine ⟨34118947126749138281197019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22745964751166092187464679 34118947126749138281197019)
    ·
      refine ⟨51178420690123707421795529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34118947126749138281197019 51178420690123707421795529)
      ·
        refine ⟨38383815517592780566346647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51178420690123707421795529 38383815517592780566346647)
        ·
          refine ⟨57575723276389170849519971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38383815517592780566346647 57575723276389170849519971)
          ·
            refine ⟨86363584914583756274279957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57575723276389170849519971 86363584914583756274279957)
            ·
              refine ⟨4048293042871113575356873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86363584914583756274279957 4048293042871113575356873)
              ·
                refine ⟨3036219782153335181517655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048293042871113575356873 3036219782153335181517655)
                ·
                  refine ⟨4554329673230002772276483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036219782153335181517655 4554329673230002772276483)
                  ·
                    refine ⟨6831494509845004158414725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554329673230002772276483 6831494509845004158414725)
                    ·
                      refine ⟨1280905220595938279702761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6831494509845004158414725 1280905220595938279702761)
                      ·
                        rfl

theorem cell23_2494554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_2494554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494554 prefixEnd_2494554 := by exact prefixLift 2494554
  have htrace : WordTrace (prefixWord ++ tailWord_2494554) baseStart_2494554 baseEnd_2494554 := by
    simpa [prefixWord, tailWord_2494554, baseEnd_2494554] using wordTrace_append hprefix tailTrace_2494554
  have hstable : (prefixWord ++ tailWord_2494554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494554).length < 2 ^ (prefixWord ++ tailWord_2494554).sum := by decide
  have hdescent : baseEnd_2494554 < baseStart_2494554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494567 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2494567 : Nat := 118140960795 + 2494567 * 2 ^ 59
def prefixEnd_2494567 : Nat := 4983230072969 + 3 ^ 40 * 2494567 * 2
def baseEnd_2494567 : Nat := 1280911895844446728840201

theorem tailTrace_2494567 : CollatzResearch.WordTrace tailWord_2494567 prefixEnd_2494567 1280911895844446728840201 := by
  unfold tailWord_2494567
  simp only [CollatzResearch.WordTrace]
  refine ⟨90984333153617271970081955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60656222102411514646721303 90984333153617271970081955)
  ·
    refine ⟨136476499730425907955122933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90984333153617271970081955 136476499730425907955122933)
    ·
      refine ⟨12794671849727428870792775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136476499730425907955122933 12794671849727428870792775)
      ·
        refine ⟨19192007774591143306189163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12794671849727428870792775 19192007774591143306189163)
        ·
          refine ⟨28788011661886714959283745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19192007774591143306189163 28788011661886714959283745)
          ·
            refine ⟨21591008746415036219462809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28788011661886714959283745 21591008746415036219462809)
            ·
              refine ⟨16193256559811277164597107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21591008746415036219462809 16193256559811277164597107)
              ·
                refine ⟨24289884839716915746895661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16193256559811277164597107 24289884839716915746895661)
                ·
                  refine ⟨9108706814893843405085873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24289884839716915746895661 9108706814893843405085873)
                  ·
                    refine ⟨6831530111170382553814405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9108706814893843405085873 6831530111170382553814405)
                    ·
                      refine ⟨1280911895844446728840201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6831530111170382553814405 1280911895844446728840201)
                      ·
                        rfl

theorem cell23_2494567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2494567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494567 prefixEnd_2494567 := by exact prefixLift 2494567
  have htrace : WordTrace (prefixWord ++ tailWord_2494567) baseStart_2494567 baseEnd_2494567 := by
    simpa [prefixWord, tailWord_2494567, baseEnd_2494567] using wordTrace_append hprefix tailTrace_2494567
  have hstable : (prefixWord ++ tailWord_2494567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494567).length < 2 ^ (prefixWord ++ tailWord_2494567).sum := by decide
  have hdescent : baseEnd_2494567 < baseStart_2494567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494574 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2494574 : Nat := 118140960795 + 2494574 * 2 ^ 59
def prefixEnd_2494574 : Nat := 4983230072969 + 3 ^ 40 * 2494574 * 2
def baseEnd_2494574 : Nat := 1280915490209028201452669

theorem tailTrace_2494574 : CollatzResearch.WordTrace tailWord_2494574 prefixEnd_2494574 1280915490209028201452669 := by
  unfold tailWord_2494574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373073558073989020698347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60656392309727941443724517 11373073558073989020698347)
  ·
    refine ⟨17059610337110983531047521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373073558073989020698347 17059610337110983531047521)
    ·
      refine ⟨12794707752833237648285641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17059610337110983531047521 12794707752833237648285641)
      ·
        refine ⟨9596030814624928236214231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12794707752833237648285641 9596030814624928236214231)
        ·
          refine ⟨14394046221937392354321347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9596030814624928236214231 14394046221937392354321347)
          ·
            refine ⟨21591069332906088531482021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14394046221937392354321347 21591069332906088531482021)
            ·
              refine ⟨4048325499919891599652879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21591069332906088531482021 4048325499919891599652879)
              ·
                refine ⟨6072488249879837399479319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048325499919891599652879 6072488249879837399479319)
                ·
                  refine ⟨9108732374819756099218979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072488249879837399479319 9108732374819756099218979)
                  ·
                    refine ⟨13663098562229634148828469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9108732374819756099218979 13663098562229634148828469)
                    ·
                      refine ⟨1280915490209028201452669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13663098562229634148828469 1280915490209028201452669)
                      ·
                        rfl

theorem cell23_2494574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2494574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494574 prefixEnd_2494574 := by exact prefixLift 2494574
  have htrace : WordTrace (prefixWord ++ tailWord_2494574) baseStart_2494574 baseEnd_2494574 := by
    simpa [prefixWord, tailWord_2494574, baseEnd_2494574] using wordTrace_append hprefix tailTrace_2494574
  have hstable : (prefixWord ++ tailWord_2494574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494574).length < 2 ^ (prefixWord ++ tailWord_2494574).sum := by decide
  have hdescent : baseEnd_2494574 < baseStart_2494574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494588 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_2494588 : Nat := 118140960795 + 2494588 * 2 ^ 59
def prefixEnd_2494588 : Nat := 4983230072969 + 3 ^ 40 * 2494588 * 2
def baseEnd_2494588 : Nat := 1280922678938191146677605

theorem tailTrace_2494588 : CollatzResearch.WordTrace tailWord_2494588 prefixEnd_2494588 1280922678938191146677605 := by
  unfold tailWord_2494588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45492549543270596278298209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60656732724360795037730945 45492549543270596278298209)
  ·
    refine ⟨34119412157452947208723657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45492549543270596278298209 34119412157452947208723657)
    ·
      refine ⟨25589559118089710406542743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34119412157452947208723657 25589559118089710406542743)
      ·
        refine ⟨38384338677134565609814115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25589559118089710406542743 38384338677134565609814115)
        ·
          refine ⟨57576508015701848414721173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38384338677134565609814115 57576508015701848414721173)
          ·
            refine ⟨2698898813236024144440055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57576508015701848414721173 2698898813236024144440055)
            ·
              refine ⟨4048348219854036216660083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698898813236024144440055 4048348219854036216660083)
              ·
                refine ⟨6072522329781054324990125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048348219854036216660083 6072522329781054324990125)
                ·
                  refine ⟨2277195873667895371871297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6072522329781054324990125 2277195873667895371871297)
                  ·
                    refine ⟨1707896905250921528903473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277195873667895371871297 1707896905250921528903473)
                    ·
                      refine ⟨1280922678938191146677605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707896905250921528903473 1280922678938191146677605)
                      ·
                        rfl

theorem cell23_2494588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_2494588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494588 prefixEnd_2494588 := by exact prefixLift 2494588
  have htrace : WordTrace (prefixWord ++ tailWord_2494588) baseStart_2494588 baseEnd_2494588 := by
    simpa [prefixWord, tailWord_2494588, baseEnd_2494588] using wordTrace_append hprefix tailTrace_2494588
  have hstable : (prefixWord ++ tailWord_2494588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494588).length < 2 ^ (prefixWord ++ tailWord_2494588).sum := by decide
  have hdescent : baseEnd_2494588 < baseStart_2494588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494667 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 7]
def baseStart_2494667 : Nat := 118140960795 + 2494667 * 2 ^ 59
def prefixEnd_2494667 : Nat := 4983230072969 + 3 ^ 40 * 2494667 * 2
def baseEnd_2494667 : Nat := 142329249323321815287749

theorem tailTrace_2494667 : CollatzResearch.WordTrace tailWord_2494667 prefixEnd_2494667 142329249323321815287749 := by
  unfold tailWord_2494667
  simp only [CollatzResearch.WordTrace]
  refine ⟨90987980453254989048722255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60658653635503326032481503 90987980453254989048722255)
  ·
    refine ⟨136481970679882483573083383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90987980453254989048722255 136481970679882483573083383)
    ·
      refine ⟨204722956019823725359625075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136481970679882483573083383 204722956019823725359625075)
      ·
        refine ⟨307084434029735588039437613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204722956019823725359625075 307084434029735588039437613)
        ·
          refine ⟨115156662761150845514789105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307084434029735588039437613 115156662761150845514789105)
          ·
            refine ⟨86367497070863134136091829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115156662761150845514789105 86367497070863134136091829)
            ·
              refine ⟨8096952850393418825258609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86367497070863134136091829 8096952850393418825258609)
              ·
                refine ⟨6072714637795064118943957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096952850393418825258609 6072714637795064118943957)
                ·
                  refine ⟨142329249323321815287749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6072714637795064118943957 142329249323321815287749)
                  ·
                    rfl

theorem cell23_2494667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 7].length) (baseStart_2494667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494667 prefixEnd_2494667 := by exact prefixLift 2494667
  have htrace : WordTrace (prefixWord ++ tailWord_2494667) baseStart_2494667 baseEnd_2494667 := by
    simpa [prefixWord, tailWord_2494667, baseEnd_2494667] using wordTrace_append hprefix tailTrace_2494667
  have hstable : (prefixWord ++ tailWord_2494667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494667).length < 2 ^ (prefixWord ++ tailWord_2494667).sum := by decide
  have hdescent : baseEnd_2494667 < baseStart_2494667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494695 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2494695 : Nat := 118140960795 + 2494695 * 2 ^ 59
def prefixEnd_2494695 : Nat := 4983230072969 + 3 ^ 40 * 2494695 * 2
def baseEnd_2494695 : Nat := 1280977621368222228039613

theorem tailTrace_2494695 : CollatzResearch.WordTrace tailWord_2494695 prefixEnd_2494695 1280977621368222228039613 := by
  unfold tailWord_2494695
  simp only [CollatzResearch.WordTrace]
  refine ⟨90989001697153549830741539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60659334464769033220494359 90989001697153549830741539)
  ·
    refine ⟨136483502545730324746112309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90989001697153549830741539 136483502545730324746112309)
    ·
      refine ⟨12795328363662217944948029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136483502545730324746112309 12795328363662217944948029)
      ·
        refine ⟨4798248136373331729355511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12795328363662217944948029 4798248136373331729355511)
        ·
          refine ⟨7197372204559997594033267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798248136373331729355511 7197372204559997594033267)
          ·
            refine ⟨10796058306839996391049901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197372204559997594033267 10796058306839996391049901)
            ·
              refine ⟨4048521865064998646643713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10796058306839996391049901 4048521865064998646643713)
              ·
                refine ⟨3036391398798748984982785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048521865064998646643713 3036391398798748984982785)
                ·
                  refine ⟨2277293549099061738737089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036391398798748984982785 2277293549099061738737089)
                  ·
                    refine ⟨1707970161824296304052817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277293549099061738737089 1707970161824296304052817)
                    ·
                      refine ⟨1280977621368222228039613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707970161824296304052817 1280977621368222228039613)
                      ·
                        rfl

theorem cell23_2494695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2494695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494695 prefixEnd_2494695 := by exact prefixLift 2494695
  have htrace : WordTrace (prefixWord ++ tailWord_2494695) baseStart_2494695 baseEnd_2494695 := by
    simpa [prefixWord, tailWord_2494695, baseEnd_2494695] using wordTrace_append hprefix tailTrace_2494695
  have hstable : (prefixWord ++ tailWord_2494695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494695).length < 2 ^ (prefixWord ++ tailWord_2494695).sum := by decide
  have hdescent : baseEnd_2494695 < baseStart_2494695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494701 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2494701 : Nat := 118140960795 + 2494701 * 2 ^ 59
def prefixEnd_2494701 : Nat := 4983230072969 + 3 ^ 40 * 2494701 * 2
def baseEnd_2494701 : Nat := 142331189139127689396065

theorem tailTrace_2494701 : CollatzResearch.WordTrace tailWord_2494701 prefixEnd_2494701 142331189139127689396065 := by
  unfold tailWord_2494701
  simp only [CollatzResearch.WordTrace]
  refine ⟨90989220535131812855459957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60659480356754541903639971 90989220535131812855459957)
  ·
    refine ⟨8530239425168607455199371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90989220535131812855459957 8530239425168607455199371)
    ·
      refine ⟨12795359137752911182799057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530239425168607455199371 12795359137752911182799057)
      ·
        refine ⟨9596519353314683387099293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12795359137752911182799057 9596519353314683387099293)
        ·
          refine ⟨3598694757493006270162235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9596519353314683387099293 3598694757493006270162235)
          ·
            refine ⟨5398042136239509405243353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598694757493006270162235 5398042136239509405243353)
            ·
              refine ⟨4048531602179632053932515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398042136239509405243353 4048531602179632053932515)
              ·
                refine ⟨6072797403269448080898773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048531602179632053932515 6072797403269448080898773)
                ·
                  refine ⟨142331189139127689396065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6072797403269448080898773 142331189139127689396065)
                  ·
                    rfl

theorem cell23_2494701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2494701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494701 prefixEnd_2494701 := by exact prefixLift 2494701
  have htrace : WordTrace (prefixWord ++ tailWord_2494701) baseStart_2494701 baseEnd_2494701 := by
    simpa [prefixWord, tailWord_2494701, baseEnd_2494701] using wordTrace_append hprefix tailTrace_2494701
  have hstable : (prefixWord ++ tailWord_2494701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494701).length < 2 ^ (prefixWord ++ tailWord_2494701).sum := by decide
  have hdescent : baseEnd_2494701 < baseStart_2494701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494704 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2]
def baseStart_2494704 : Nat := 118140960795 + 2494704 * 2 ^ 59
def prefixEnd_2494704 : Nat := 4983230072969 + 3 ^ 40 * 2494704 * 2
def baseEnd_2494704 : Nat := 1280982242694112692827071

theorem tailTrace_2494704 : CollatzResearch.WordTrace tailWord_2494704 prefixEnd_2494704 1280982242694112692827071 := by
  unfold tailWord_2494704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45494664977060472183909583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60659553302747296245212777 45494664977060472183909583)
  ·
    refine ⟨68241997465590708275864375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45494664977060472183909583 68241997465590708275864375)
    ·
      refine ⟨102362996198386062413796563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68241997465590708275864375 102362996198386062413796563)
      ·
        refine ⟨153544494297579093620694845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102362996198386062413796563 153544494297579093620694845)
        ·
          refine ⟨57579185361592160107760567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153544494297579093620694845 57579185361592160107760567)
          ·
            refine ⟨86368778042388240161640851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57579185361592160107760567 86368778042388240161640851)
            ·
              refine ⟨129553167063582360242461277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86368778042388240161640851 129553167063582360242461277)
              ·
                refine ⟨48582437648843385090922979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129553167063582360242461277 48582437648843385090922979)
                ·
                  refine ⟨72873656473265077636384469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48582437648843385090922979 72873656473265077636384469)
                  ·
                    refine ⟨1707976323592150257102761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 72873656473265077636384469 1707976323592150257102761)
                    ·
                      refine ⟨1280982242694112692827071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1707976323592150257102761 1280982242694112692827071)
                      ·
                        rfl

theorem cell23_2494704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2].length) (baseStart_2494704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494704 prefixEnd_2494704 := by exact prefixLift 2494704
  have htrace : WordTrace (prefixWord ++ tailWord_2494704) baseStart_2494704 baseEnd_2494704 := by
    simpa [prefixWord, tailWord_2494704, baseEnd_2494704] using wordTrace_append hprefix tailTrace_2494704
  have hstable : (prefixWord ++ tailWord_2494704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494704).length < 2 ^ (prefixWord ++ tailWord_2494704).sum := by decide
  have hdescent : baseEnd_2494704 < baseStart_2494704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494707 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_2494707 : Nat := 118140960795 + 2494707 * 2 ^ 59
def prefixEnd_2494707 : Nat := 4983230072969 + 3 ^ 40 * 2494707 * 2
def baseEnd_2494707 : Nat := 1280983783136076181089557

theorem tailTrace_2494707 : CollatzResearch.WordTrace tailWord_2494707 prefixEnd_2494707 1280983783136076181089557 := by
  unfold tailWord_2494707
  simp only [CollatzResearch.WordTrace]
  refine ⟨90989439373110075880178375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60659626248740050586785583 90989439373110075880178375)
  ·
    refine ⟨136484159059665113820267563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90989439373110075880178375 136484159059665113820267563)
    ·
      refine ⟨204726238589497670730401345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136484159059665113820267563 204726238589497670730401345)
      ·
        refine ⟨153544678942123253047801009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204726238589497670730401345 153544678942123253047801009)
        ·
          refine ⟨115158509206592439785850757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153544678942123253047801009 115158509206592439785850757)
          ·
            refine ⟨21592220476236082459847017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115158509206592439785850757 21592220476236082459847017)
            ·
              refine ⟨16194165357177061844885263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21592220476236082459847017 16194165357177061844885263)
              ·
                refine ⟨24291248035765592767327895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16194165357177061844885263 24291248035765592767327895)
                ·
                  refine ⟨36436872053648389150991843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24291248035765592767327895 36436872053648389150991843)
                  ·
                    refine ⟨54655308080472583726487765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36436872053648389150991843 54655308080472583726487765)
                    ·
                      refine ⟨1280983783136076181089557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54655308080472583726487765 1280983783136076181089557)
                      ·
                        rfl

theorem cell23_2494707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_2494707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494707 prefixEnd_2494707 := by exact prefixLift 2494707
  have htrace : WordTrace (prefixWord ++ tailWord_2494707) baseStart_2494707 baseEnd_2494707 := by
    simpa [prefixWord, tailWord_2494707, baseEnd_2494707] using wordTrace_append hprefix tailTrace_2494707
  have hstable : (prefixWord ++ tailWord_2494707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494707).length < 2 ^ (prefixWord ++ tailWord_2494707).sum := by decide
  have hdescent : baseEnd_2494707 < baseStart_2494707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494734 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2494734 : Nat := 118140960795 + 2494734 * 2 ^ 59
def prefixEnd_2494734 : Nat := 4983230072969 + 3 ^ 40 * 2494734 * 2
def baseEnd_2494734 : Nat := 1280997647113747575451933

theorem tailTrace_2494734 : CollatzResearch.WordTrace tailWord_2494734 prefixEnd_2494734 1280997647113747575451933 := by
  unfold tailWord_2494734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373803018001532436426407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60660282762674839660940837 11373803018001532436426407)
  ·
    refine ⟨17060704527002298654639611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373803018001532436426407 17060704527002298654639611)
    ·
      refine ⟨25591056790503447981959417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17060704527002298654639611 25591056790503447981959417)
      ·
        refine ⟨19193292592877585986469563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25591056790503447981959417 19193292592877585986469563)
        ·
          refine ⟨28789938889316378979704345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19193292592877585986469563 28789938889316378979704345)
          ·
            refine ⟨21592454166987284234778259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28789938889316378979704345 21592454166987284234778259)
            ·
              refine ⟨32388681250480926352167389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21592454166987284234778259 32388681250480926352167389)
              ·
                refine ⟨12145755468930347382062771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32388681250480926352167389 12145755468930347382062771)
                ·
                  refine ⟨18218633203395521073094157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12145755468930347382062771 18218633203395521073094157)
                  ·
                    refine ⟨6831987451273320402410309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18218633203395521073094157 6831987451273320402410309)
                    ·
                      refine ⟨1280997647113747575451933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6831987451273320402410309 1280997647113747575451933)
                      ·
                        rfl

theorem cell23_2494734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2494734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494734 prefixEnd_2494734 := by exact prefixLift 2494734
  have htrace : WordTrace (prefixWord ++ tailWord_2494734) baseStart_2494734 baseEnd_2494734 := by
    simpa [prefixWord, tailWord_2494734, baseEnd_2494734] using wordTrace_append hprefix tailTrace_2494734
  have hstable : (prefixWord ++ tailWord_2494734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494734).length < 2 ^ (prefixWord ++ tailWord_2494734).sum := by decide
  have hdescent : baseEnd_2494734 < baseStart_2494734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494747 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_2494747 : Nat := 118140960795 + 2494747 * 2 ^ 59
def prefixEnd_2494747 : Nat := 4983230072969 + 3 ^ 40 * 2494747 * 2
def baseEnd_2494747 : Nat := 1281004322362256024589373

theorem tailTrace_2494747 : CollatzResearch.WordTrace tailWord_2494747 prefixEnd_2494747 1281004322362256024589373 := by
  unfold tailWord_2494747
  simp only [CollatzResearch.WordTrace]
  refine ⟨90990898292965162711634495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60660598861976775141089663 90990898292965162711634495)
  ·
    refine ⟨136486347439447744067451743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90990898292965162711634495 136486347439447744067451743)
    ·
      refine ⟨204729521159171616101177615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136486347439447744067451743 204729521159171616101177615)
      ·
        refine ⟨307094281738757424151766423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204729521159171616101177615 307094281738757424151766423)
        ·
          refine ⟨460641422608136136227649635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307094281738757424151766423 460641422608136136227649635)
          ·
            refine ⟨690962133912204204341474453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460641422608136136227649635 690962133912204204341474453)
            ·
              refine ⟨32388850027134572078506615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 690962133912204204341474453 32388850027134572078506615)
              ·
                refine ⟨48583275040701858117759923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32388850027134572078506615 48583275040701858117759923)
                ·
                  refine ⟨72874912561052787176639885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48583275040701858117759923 72874912561052787176639885)
                  ·
                    refine ⟨27328092210394795191239957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72874912561052787176639885 27328092210394795191239957)
                    ·
                      refine ⟨1281004322362256024589373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27328092210394795191239957 1281004322362256024589373)
                      ·
                        rfl

theorem cell23_2494747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_2494747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494747 prefixEnd_2494747 := by exact prefixLift 2494747
  have htrace : WordTrace (prefixWord ++ tailWord_2494747) baseStart_2494747 baseEnd_2494747 := by
    simpa [prefixWord, tailWord_2494747, baseEnd_2494747] using wordTrace_append hprefix tailTrace_2494747
  have hstable : (prefixWord ++ tailWord_2494747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494747).length < 2 ^ (prefixWord ++ tailWord_2494747).sum := by decide
  have hdescent : baseEnd_2494747 < baseStart_2494747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494751 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2494751 : Nat := 118140960795 + 2494751 * 2 ^ 59
def prefixEnd_2494751 : Nat := 4983230072969 + 3 ^ 40 * 2494751 * 2
def baseEnd_2494751 : Nat := 1281006376284874008939355

theorem tailTrace_2494751 : CollatzResearch.WordTrace tailWord_2494751 prefixEnd_2494751 1281006376284874008939355 := by
  unfold tailWord_2494751
  simp only [CollatzResearch.WordTrace]
  refine ⟨90991044184950671394780107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60660696123300447596520071 90991044184950671394780107)
  ·
    refine ⟨136486566277426007092170161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90991044184950671394780107 136486566277426007092170161)
    ·
      refine ⟨102364924708069505319127621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136486566277426007092170161 102364924708069505319127621)
      ·
        refine ⟨19193423382763032247336429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102364924708069505319127621 19193423382763032247336429)
        ·
          refine ⟨7197533768536137092751161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19193423382763032247336429 7197533768536137092751161)
          ·
            refine ⟨5398150326402102819563371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7197533768536137092751161 5398150326402102819563371)
            ·
              refine ⟨8097225489603154229345057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398150326402102819563371 8097225489603154229345057)
              ·
                refine ⟨6072919117202365672008793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8097225489603154229345057 6072919117202365672008793)
                ·
                  refine ⟨4554689337901774254006595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6072919117202365672008793 4554689337901774254006595)
                  ·
                    refine ⟨6832034006852661381009893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554689337901774254006595 6832034006852661381009893)
                    ·
                      refine ⟨1281006376284874008939355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6832034006852661381009893 1281006376284874008939355)
                      ·
                        rfl

theorem cell23_2494751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2494751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494751 prefixEnd_2494751 := by exact prefixLift 2494751
  have htrace : WordTrace (prefixWord ++ tailWord_2494751) baseStart_2494751 baseEnd_2494751 := by
    simpa [prefixWord, tailWord_2494751, baseEnd_2494751] using wordTrace_append hprefix tailTrace_2494751
  have hstable : (prefixWord ++ tailWord_2494751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494751).length < 2 ^ (prefixWord ++ tailWord_2494751).sum := by decide
  have hdescent : baseEnd_2494751 < baseStart_2494751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494812 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2494812 : Nat := 118140960795 + 2494812 * 2 ^ 59
def prefixEnd_2494812 : Nat := 4983230072969 + 3 ^ 40 * 2494812 * 2
def baseEnd_2494812 : Nat := 427012566201599423425525

theorem tailTrace_2494812 : CollatzResearch.WordTrace tailWord_2494812 prefixEnd_2494812 427012566201599423425525 := by
  unfold tailWord_2494812
  simp only [CollatzResearch.WordTrace]
  refine ⟨45496634518864839406375345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60662179358486452541833793 45496634518864839406375345)
  ·
    refine ⟨34122475889148629554781509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45496634518864839406375345 34122475889148629554781509)
    ·
      refine ⟨6397964229215368041521533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34122475889148629554781509 6397964229215368041521533)
      ·
        refine ⟨2399236585955763015570575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6397964229215368041521533 2399236585955763015570575)
        ·
          refine ⟨3598854878933644523355863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399236585955763015570575 3598854878933644523355863)
          ·
            refine ⟨5398282318400466785033795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598854878933644523355863 5398282318400466785033795)
            ·
              refine ⟨8097423477600700177550693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398282318400466785033795 8097423477600700177550693)
              ·
                refine ⟨1518266902050131283290755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8097423477600700177550693 1518266902050131283290755)
                ·
                  refine ⟨2277400353075196924936133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518266902050131283290755 2277400353075196924936133)
                  ·
                    refine ⟨427012566201599423425525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277400353075196924936133 427012566201599423425525)
                    ·
                      rfl

theorem cell23_2494812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2494812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494812 prefixEnd_2494812 := by exact prefixLift 2494812
  have htrace : WordTrace (prefixWord ++ tailWord_2494812) baseStart_2494812 baseEnd_2494812 := by
    simpa [prefixWord, tailWord_2494812, baseEnd_2494812] using wordTrace_append hprefix tailTrace_2494812
  have hstable : (prefixWord ++ tailWord_2494812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494812).length < 2 ^ (prefixWord ++ tailWord_2494812).sum := by decide
  have hdescent : baseEnd_2494812 < baseStart_2494812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494841 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2494841 : Nat := 118140960795 + 2494841 * 2 ^ 59
def prefixEnd_2494841 : Nat := 4983230072969 + 3 ^ 40 * 2494841 * 2
def baseEnd_2494841 : Nat := 1281052589543778656813941

theorem tailTrace_2494841 : CollatzResearch.WordTrace tailWord_2494841 prefixEnd_2494841 1281052589543778656813941 := by
  unfold tailWord_2494841
  simp only [CollatzResearch.WordTrace]
  refine ⟨90994326754624616765556377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60662884503083077843704251 90994326754624616765556377)
  ·
    refine ⟨68245745065968462574167283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90994326754624616765556377 68245745065968462574167283)
    ·
      refine ⟨102368617598952693861250925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68245745065968462574167283 102368617598952693861250925)
      ·
        refine ⟨38388231599607260197969097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102368617598952693861250925 38388231599607260197969097)
        ·
          refine ⟨28791173699705445148476823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38388231599607260197969097 28791173699705445148476823)
          ·
            refine ⟨43186760549558167722715235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28791173699705445148476823 43186760549558167722715235)
            ·
              refine ⟨64780140824337251584072853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43186760549558167722715235 64780140824337251584072853)
              ·
                refine ⟨3036569101140808668003415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64780140824337251584072853 3036569101140808668003415)
                ·
                  refine ⟨4554853651711213002005123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036569101140808668003415 4554853651711213002005123)
                  ·
                    refine ⟨6832280477566819503007685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554853651711213002005123 6832280477566819503007685)
                    ·
                      refine ⟨1281052589543778656813941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6832280477566819503007685 1281052589543778656813941)
                      ·
                        rfl

theorem cell23_2494841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2494841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494841 prefixEnd_2494841 := by exact prefixLift 2494841
  have htrace : WordTrace (prefixWord ++ tailWord_2494841) baseStart_2494841 baseEnd_2494841 := by
    simpa [prefixWord, tailWord_2494841, baseEnd_2494841] using wordTrace_append hprefix tailTrace_2494841
  have hstable : (prefixWord ++ tailWord_2494841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494841).length < 2 ^ (prefixWord ++ tailWord_2494841).sum := by decide
  have hdescent : baseEnd_2494841 < baseStart_2494841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494844 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2494844 : Nat := 118140960795 + 2494844 * 2 ^ 59
def prefixEnd_2494844 : Nat := 4983230072969 + 3 ^ 40 * 2494844 * 2
def baseEnd_2494844 : Nat := 1281054129985742145076427

theorem tailTrace_2494844 : CollatzResearch.WordTrace tailWord_2494844 prefixEnd_2494844 1281054129985742145076427 := by
  unfold tailWord_2494844
  simp only [CollatzResearch.WordTrace]
  refine ⟨45497218086806874138957793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60662957449075832185277057 45497218086806874138957793)
  ·
    refine ⟨34122913565105155604218345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45497218086806874138957793 34122913565105155604218345)
    ·
      refine ⟨25592185173828866703163759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34122913565105155604218345 25592185173828866703163759)
      ·
        refine ⟨38388277760743300054745639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25592185173828866703163759 38388277760743300054745639)
        ·
          refine ⟨57582416641114950082118459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38388277760743300054745639 57582416641114950082118459)
          ·
            refine ⟨86373624961672425123177689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57582416641114950082118459 86373624961672425123177689)
            ·
              refine ⟨64780218721254318842383267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86373624961672425123177689 64780218721254318842383267)
              ·
                refine ⟨97170328081881478263574901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64780218721254318842383267 97170328081881478263574901)
                ·
                  refine ⟨9109718257676388587210147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97170328081881478263574901 9109718257676388587210147)
                  ·
                    refine ⟨13664577386514582880815221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9109718257676388587210147 13664577386514582880815221)
                    ·
                      refine ⟨1281054129985742145076427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13664577386514582880815221 1281054129985742145076427)
                      ·
                        rfl

theorem cell23_2494844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2494844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494844 prefixEnd_2494844 := by exact prefixLift 2494844
  have htrace : WordTrace (prefixWord ++ tailWord_2494844) baseStart_2494844 baseEnd_2494844 := by
    simpa [prefixWord, tailWord_2494844, baseEnd_2494844] using wordTrace_append hprefix tailTrace_2494844
  have hstable : (prefixWord ++ tailWord_2494844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494844).length < 2 ^ (prefixWord ++ tailWord_2494844).sum := by decide
  have hdescent : baseEnd_2494844 < baseStart_2494844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494845 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_2494845 : Nat := 118140960795 + 2494845 * 2 ^ 59
def prefixEnd_2494845 : Nat := 4983230072969 + 3 ^ 40 * 2494845 * 2
def baseEnd_2494845 : Nat := 1281054643466396641163923

theorem tailTrace_2494845 : CollatzResearch.WordTrace tailWord_2494845 prefixEnd_2494845 1281054643466396641163923 := by
  unfold tailWord_2494845
  simp only [CollatzResearch.WordTrace]
  refine ⟨90994472646610125448701989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60662981764406750299134659 90994472646610125448701989)
  ·
    refine ⟨17061463621239398521631623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90994472646610125448701989 17061463621239398521631623)
    ·
      refine ⟨25592195431859097782447435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17061463621239398521631623 25592195431859097782447435)
      ·
        refine ⟨38388293147788646673671153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25592195431859097782447435 38388293147788646673671153)
        ·
          refine ⟨28791219860841485005253365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38388293147788646673671153 28791219860841485005253365)
          ·
            refine ⟨2699176861953889219242503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28791219860841485005253365 2699176861953889219242503)
            ·
              refine ⟨4048765292930833828863755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699176861953889219242503 4048765292930833828863755)
              ·
                refine ⟨6073147939396250743295633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048765292930833828863755 6073147939396250743295633)
                ·
                  refine ⟨4554860954547188057471725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6073147939396250743295633 4554860954547188057471725)
                  ·
                    refine ⟨1708072857955195521551897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4554860954547188057471725 1708072857955195521551897)
                    ·
                      refine ⟨1281054643466396641163923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708072857955195521551897 1281054643466396641163923)
                      ·
                        rfl

theorem cell23_2494845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_2494845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494845 prefixEnd_2494845 := by exact prefixLift 2494845
  have htrace : WordTrace (prefixWord ++ tailWord_2494845) baseStart_2494845 baseEnd_2494845 := by
    simpa [prefixWord, tailWord_2494845, baseEnd_2494845] using wordTrace_append hprefix tailTrace_2494845
  have hstable : (prefixWord ++ tailWord_2494845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494845).length < 2 ^ (prefixWord ++ tailWord_2494845).sum := by decide
  have hdescent : baseEnd_2494845 < baseStart_2494845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494878 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2494878 : Nat := 118140960795 + 2494878 * 2 ^ 59
def prefixEnd_2494878 : Nat := 4983230072969 + 3 ^ 40 * 2494878 * 2
def baseEnd_2494878 : Nat := 1281071588327995012051271

theorem tailTrace_2494878 : CollatzResearch.WordTrace tailWord_2494878 prefixEnd_2494878 1281071588327995012051271 := by
  unfold tailWord_2494878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11374459531936321510581661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60663784170327048056435525 11374459531936321510581661)
  ·
    refine ⟨4265422324476120566468123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11374459531936321510581661 4265422324476120566468123)
    ·
      refine ⟨6398133486714180849702185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265422324476120566468123 6398133486714180849702185)
      ·
        refine ⟨4798600115035635637276639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6398133486714180849702185 4798600115035635637276639)
        ·
          refine ⟨7197900172553453455914959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798600115035635637276639 7197900172553453455914959)
          ·
            refine ⟨10796850258830180183872439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7197900172553453455914959 10796850258830180183872439)
            ·
              refine ⟨16195275388245270275808659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10796850258830180183872439 16195275388245270275808659)
              ·
                refine ⟨24292913082367905413712989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16195275388245270275808659 24292913082367905413712989)
                ·
                  refine ⟨9109842405887964530142371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24292913082367905413712989 9109842405887964530142371)
                  ·
                    refine ⟨13664763608831946795213557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9109842405887964530142371 13664763608831946795213557)
                    ·
                      refine ⟨1281071588327995012051271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13664763608831946795213557 1281071588327995012051271)
                      ·
                        rfl

theorem cell23_2494878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2494878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494878 prefixEnd_2494878 := by exact prefixLift 2494878
  have htrace : WordTrace (prefixWord ++ tailWord_2494878) baseStart_2494878 baseEnd_2494878 := by
    simpa [prefixWord, tailWord_2494878, baseEnd_2494878] using wordTrace_append hprefix tailTrace_2494878
  have hstable : (prefixWord ++ tailWord_2494878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494878).length < 2 ^ (prefixWord ++ tailWord_2494878).sum := by decide
  have hdescent : baseEnd_2494878 < baseStart_2494878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494888 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2494888 : Nat := 118140960795 + 2494888 * 2 ^ 59
def prefixEnd_2494888 : Nat := 4983230072969 + 3 ^ 40 * 2494888 * 2
def baseEnd_2494888 : Nat := 1281076723134539972926225

theorem tailTrace_2494888 : CollatzResearch.WordTrace tailWord_2494888 prefixEnd_2494888 1281076723134539972926225 := by
  unfold tailWord_2494888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45498020492727171896258659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60664027323636229195011545 45498020492727171896258659)
  ·
    refine ⟨68247030739090757844387989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45498020492727171896258659 68247030739090757844387989)
    ·
      refine ⟨3199079565894879273955687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68247030739090757844387989 3199079565894879273955687)
      ·
        refine ⟨4798619348842318910933531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199079565894879273955687 4798619348842318910933531)
        ·
          refine ⟨7197929023263478366400297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798619348842318910933531 7197929023263478366400297)
          ·
            refine ⟨5398446767447608774800223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7197929023263478366400297 5398446767447608774800223)
            ·
              refine ⟨8097670151171413162200335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398446767447608774800223 8097670151171413162200335)
              ·
                refine ⟨12146505226757119743300503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8097670151171413162200335 12146505226757119743300503)
                ·
                  refine ⟨18219757840135679614950755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12146505226757119743300503 18219757840135679614950755)
                  ·
                    refine ⟨27329636760203519422426133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18219757840135679614950755 27329636760203519422426133)
                    ·
                      refine ⟨1281076723134539972926225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27329636760203519422426133 1281076723134539972926225)
                      ·
                        rfl

theorem cell23_2494888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2494888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494888 prefixEnd_2494888 := by exact prefixLift 2494888
  have htrace : WordTrace (prefixWord ++ tailWord_2494888) baseStart_2494888 baseEnd_2494888 := by
    simpa [prefixWord, tailWord_2494888, baseEnd_2494888] using wordTrace_append hprefix tailTrace_2494888
  have hstable : (prefixWord ++ tailWord_2494888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494888).length < 2 ^ (prefixWord ++ tailWord_2494888).sum := by decide
  have hdescent : baseEnd_2494888 < baseStart_2494888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494909 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_2494909 : Nat := 118140960795 + 2494909 * 2 ^ 59
def prefixEnd_2494909 : Nat := 4983230072969 + 3 ^ 40 * 2494909 * 2
def baseEnd_2494909 : Nat := 1281087506228284390763629

theorem tailTrace_2494909 : CollatzResearch.WordTrace tailWord_2494909 prefixEnd_2494909 1281087506228284390763629 := by
  unfold tailWord_2494909
  simp only [CollatzResearch.WordTrace]
  refine ⟨90996806918378264379031781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60664537945585509586021187 90996806918378264379031781)
  ·
    refine ⟨17061901297195924571068459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90996806918378264379031781 17061901297195924571068459)
    ·
      refine ⟨25592851945793886856602689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17061901297195924571068459 25592851945793886856602689)
      ·
        refine ⟨19194638959345415142452017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25592851945793886856602689 19194638959345415142452017)
        ·
          refine ⟨14395979219509061356839013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19194638959345415142452017 14395979219509061356839013)
          ·
            refine ⟨2699246103657949004407315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14395979219509061356839013 2699246103657949004407315)
            ·
              refine ⟨4048869155486923506610973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699246103657949004407315 4048869155486923506610973)
              ·
                refine ⟨1518325933307596314979115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4048869155486923506610973 1518325933307596314979115)
                ·
                  refine ⟨2277488899961394472468673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518325933307596314979115 2277488899961394472468673)
                  ·
                    refine ⟨1708116674971045854351505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277488899961394472468673 1708116674971045854351505)
                    ·
                      refine ⟨1281087506228284390763629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708116674971045854351505 1281087506228284390763629)
                      ·
                        rfl

theorem cell23_2494909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_2494909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494909 prefixEnd_2494909 := by exact prefixLift 2494909
  have htrace : WordTrace (prefixWord ++ tailWord_2494909) baseStart_2494909 baseEnd_2494909 := by
    simpa [prefixWord, tailWord_2494909, baseEnd_2494909] using wordTrace_append hprefix tailTrace_2494909
  have hstable : (prefixWord ++ tailWord_2494909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494909).length < 2 ^ (prefixWord ++ tailWord_2494909).sum := by decide
  have hdescent : baseEnd_2494909 < baseStart_2494909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494941 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2494941 : Nat := 118140960795 + 2494941 * 2 ^ 59
def prefixEnd_2494941 : Nat := 4983230072969 + 3 ^ 40 * 2494941 * 2
def baseEnd_2494941 : Nat := 427034645869742755187827

theorem tailTrace_2494941 : CollatzResearch.WordTrace tailWord_2494941 prefixEnd_2494941 427034645869742755187827 := by
  unfold tailWord_2494941
  simp only [CollatzResearch.WordTrace]
  refine ⟨90997974054262333844196677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60665316036174889229464451 90997974054262333844196677)
  ·
    refine ⟨17062120135174187595786877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90997974054262333844196677 17062120135174187595786877)
    ·
      refine ⟨6398295050690320348420079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17062120135174187595786877 6398295050690320348420079)
      ·
        refine ⟨9597442576035480522630119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398295050690320348420079 9597442576035480522630119)
        ·
          refine ⟨14396163864053220783945179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9597442576035480522630119 14396163864053220783945179)
          ·
            refine ⟨21594245796079831175917769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14396163864053220783945179 21594245796079831175917769)
            ·
              refine ⟨16195684347059873381938327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21594245796079831175917769 16195684347059873381938327)
              ·
                refine ⟨24293526520589810072907491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16195684347059873381938327 24293526520589810072907491)
                ·
                  refine ⟨36440289780884715109361237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24293526520589810072907491 36440289780884715109361237)
                  ·
                    refine ⟨427034645869742755187827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36440289780884715109361237 427034645869742755187827)
                    ·
                      rfl

theorem cell23_2494941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2494941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494941 prefixEnd_2494941 := by exact prefixLift 2494941
  have htrace : WordTrace (prefixWord ++ tailWord_2494941) baseStart_2494941 baseEnd_2494941 := by
    simpa [prefixWord, tailWord_2494941, baseEnd_2494941] using wordTrace_append hprefix tailTrace_2494941
  have hstable : (prefixWord ++ tailWord_2494941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494941).length < 2 ^ (prefixWord ++ tailWord_2494941).sum := by decide
  have hdescent : baseEnd_2494941 < baseStart_2494941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494946 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2494946 : Nat := 118140960795 + 2494946 * 2 ^ 59
def prefixEnd_2494946 : Nat := 4983230072969 + 3 ^ 40 * 2494946 * 2
def baseEnd_2494946 : Nat := 1281106505012500746000959

theorem tailTrace_2494946 : CollatzResearch.WordTrace tailWord_2494946 prefixEnd_2494946 1281106505012500746000959 := by
  unfold tailWord_2494946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22749539104811054924532173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60665437612829479798752461 22749539104811054924532173)
  ·
    refine ⟨8531077164304145596699565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22749539104811054924532173 8531077164304145596699565)
    ·
      refine ⟨3199153936614054598762337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8531077164304145596699565 3199153936614054598762337)
      ·
        refine ⟨2399365452460540949071753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3199153936614054598762337 2399365452460540949071753)
        ·
          refine ⟨1799524089345405711803815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2399365452460540949071753 1799524089345405711803815)
          ·
            refine ⟨2699286134018108567705723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799524089345405711803815 2699286134018108567705723)
            ·
              refine ⟨4048929201027162851558585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699286134018108567705723 4048929201027162851558585)
              ·
                refine ⟨3036696900770372138668939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048929201027162851558585 3036696900770372138668939)
                ·
                  refine ⟨4555045351155558208003409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036696900770372138668939 4555045351155558208003409)
                  ·
                    refine ⟨3416284013366668656002557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4555045351155558208003409 3416284013366668656002557)
                    ·
                      refine ⟨1281106505012500746000959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3416284013366668656002557 1281106505012500746000959)
                      ·
                        rfl

theorem cell23_2494946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2494946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494946 prefixEnd_2494946 := by exact prefixLift 2494946
  have htrace : WordTrace (prefixWord ++ tailWord_2494946) baseStart_2494946 baseEnd_2494946 := by
    simpa [prefixWord, tailWord_2494946, baseEnd_2494946] using wordTrace_append hprefix tailTrace_2494946
  have hstable : (prefixWord ++ tailWord_2494946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494946).length < 2 ^ (prefixWord ++ tailWord_2494946).sum := by decide
  have hdescent : baseEnd_2494946 < baseStart_2494946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494951 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2494951 : Nat := 118140960795 + 2494951 * 2 ^ 59
def prefixEnd_2494951 : Nat := 4983230072969 + 3 ^ 40 * 2494951 * 2
def baseEnd_2494951 : Nat := 1281109072415773226438435

theorem tailTrace_2494951 : CollatzResearch.WordTrace tailWord_2494951 prefixEnd_2494951 1281109072415773226438435 := by
  unfold tailWord_2494951
  simp only [CollatzResearch.WordTrace]
  refine ⟨90998338784226105552060707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60665559189484070368040471 90998338784226105552060707)
  ·
    refine ⟨136497508176339158328091061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90998338784226105552060707 136497508176339158328091061)
    ·
      refine ⟨12796641391531796093258537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136497508176339158328091061 12796641391531796093258537)
      ·
        refine ⟨9597481043648847069943903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12796641391531796093258537 9597481043648847069943903)
        ·
          refine ⟨14396221565473270604915855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9597481043648847069943903 14396221565473270604915855)
          ·
            refine ⟨21594332348209905907373783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14396221565473270604915855 21594332348209905907373783)
            ·
              refine ⟨32391498522314858861060675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21594332348209905907373783 32391498522314858861060675)
              ·
                refine ⟨48587247783472288291591013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32391498522314858861060675 48587247783472288291591013)
                ·
                  refine ⟨9110108959401054054673315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48587247783472288291591013 9110108959401054054673315)
                  ·
                    refine ⟨13665163439101581082009973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9110108959401054054673315 13665163439101581082009973)
                    ·
                      refine ⟨1281109072415773226438435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13665163439101581082009973 1281109072415773226438435)
                      ·
                        rfl

theorem cell23_2494951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2494951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494951 prefixEnd_2494951 := by exact prefixLift 2494951
  have htrace : WordTrace (prefixWord ++ tailWord_2494951) baseStart_2494951 baseEnd_2494951 := by
    simpa [prefixWord, tailWord_2494951, baseEnd_2494951] using wordTrace_append hprefix tailTrace_2494951
  have hstable : (prefixWord ++ tailWord_2494951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494951).length < 2 ^ (prefixWord ++ tailWord_2494951).sum := by decide
  have hdescent : baseEnd_2494951 < baseStart_2494951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494952 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2494952 : Nat := 118140960795 + 2494952 * 2 ^ 59
def prefixEnd_2494952 : Nat := 4983230072969 + 3 ^ 40 * 2494952 * 2
def baseEnd_2494952 : Nat := 1281109585896427722525931

theorem tailTrace_2494952 : CollatzResearch.WordTrace tailWord_2494952 prefixEnd_2494952 1281109585896427722525931 := by
  unfold tailWord_2494952
  simp only [CollatzResearch.WordTrace]
  refine ⟨45499187628611241361423555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60665583504814988481898073 45499187628611241361423555)
  ·
    refine ⟨68248781442916862042135333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45499187628611241361423555 68248781442916862042135333)
    ·
      refine ⟨12796646520546911632900375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68248781442916862042135333 12796646520546911632900375)
      ·
        refine ⟨19194969780820367449350563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12796646520546911632900375 19194969780820367449350563)
        ·
          refine ⟨28792454671230551174025845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19194969780820367449350563 28792454671230551174025845)
          ·
            refine ⟨2699292625427864172564923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28792454671230551174025845 2699292625427864172564923)
            ·
              refine ⟨4048938938141796258847385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699292625427864172564923 4048938938141796258847385)
              ·
                refine ⟨3036704203606347194135539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4048938938141796258847385 3036704203606347194135539)
                ·
                  refine ⟨4555056305409520791203309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036704203606347194135539 4555056305409520791203309)
                  ·
                    refine ⟨1708146114528570296701241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4555056305409520791203309 1708146114528570296701241)
                    ·
                      refine ⟨1281109585896427722525931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708146114528570296701241 1281109585896427722525931)
                      ·
                        rfl

theorem cell23_2494952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2494952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494952 prefixEnd_2494952 := by exact prefixLift 2494952
  have htrace : WordTrace (prefixWord ++ tailWord_2494952) baseStart_2494952 baseEnd_2494952 := by
    simpa [prefixWord, tailWord_2494952, baseEnd_2494952] using wordTrace_append hprefix tailTrace_2494952
  have hstable : (prefixWord ++ tailWord_2494952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494952).length < 2 ^ (prefixWord ++ tailWord_2494952).sum := by decide
  have hdescent : baseEnd_2494952 < baseStart_2494952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2494982 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2494982 : Nat := 118140960795 + 2494982 * 2 ^ 59
def prefixEnd_2494982 : Nat := 4983230072969 + 3 ^ 40 * 2494982 * 2
def baseEnd_2494982 : Nat := 1281124990316062605150793

theorem tailTrace_2494982 : CollatzResearch.WordTrace tailWord_2494982 prefixEnd_2494982 1281124990316062605150793 := by
  unfold tailWord_2494982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843733420222306182701225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60666312964742531897626133 2843733420222306182701225)
  ·
    refine ⟨2132800065166729637025919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2843733420222306182701225 2132800065166729637025919)
    ·
      refine ⟨3199200097750094455538879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2132800065166729637025919 3199200097750094455538879)
      ·
        refine ⟨4798800146625141683308319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199200097750094455538879 4798800146625141683308319)
        ·
          refine ⟨7198200219937712524962479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798800146625141683308319 7198200219937712524962479)
          ·
            refine ⟨10797300329906568787443719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198200219937712524962479 10797300329906568787443719)
            ·
              refine ⟨16195950494859853181165579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10797300329906568787443719 16195950494859853181165579)
              ·
                refine ⟨24293925742289779771748369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16195950494859853181165579 24293925742289779771748369)
                ·
                  refine ⟨18220444306717334828811277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24293925742289779771748369 18220444306717334828811277)
                  ·
                    refine ⟨6832666615019000560804229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18220444306717334828811277 6832666615019000560804229)
                    ·
                      refine ⟨1281124990316062605150793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6832666615019000560804229 1281124990316062605150793)
                      ·
                        rfl

theorem cell23_2494982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2494982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2494982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2494982 prefixEnd_2494982 := by exact prefixLift 2494982
  have htrace : WordTrace (prefixWord ++ tailWord_2494982) baseStart_2494982 baseEnd_2494982 := by
    simpa [prefixWord, tailWord_2494982, baseEnd_2494982] using wordTrace_append hprefix tailTrace_2494982
  have hstable : (prefixWord ++ tailWord_2494982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2494982).length < 2 ^ (prefixWord ++ tailWord_2494982).sum := by decide
  have hdescent : baseEnd_2494982 < baseStart_2494982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2494982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495018 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2495018 : Nat := 118140960795 + 2495018 * 2 ^ 59
def prefixEnd_2495018 : Nat := 4983230072969 + 3 ^ 40 * 2495018 * 2
def baseEnd_2495018 : Nat := 427047825206541488100209

theorem tailTrace_2495018 : CollatzResearch.WordTrace tailWord_2495018 prefixEnd_2495018 427047825206541488100209 := by
  unfold tailWord_2495018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22750195618745843998687427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60667188316655583996499805 22750195618745843998687427)
  ·
    refine ⟨34125293428118765998031141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22750195618745843998687427 34125293428118765998031141)
    ·
      refine ⟨6398492517772268624630839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34125293428118765998031141 6398492517772268624630839)
      ·
        refine ⟨9597738776658402936946259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398492517772268624630839 9597738776658402936946259)
        ·
          refine ⟨14396608164987604405419389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9597738776658402936946259 14396608164987604405419389)
          ·
            refine ⟨5398728061870351652032271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14396608164987604405419389 5398728061870351652032271)
            ·
              refine ⟨8098092092805527478048407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398728061870351652032271 8098092092805527478048407)
              ·
                refine ⟨12147138139208291217072611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8098092092805527478048407 12147138139208291217072611)
                ·
                  refine ⟨18220707208812436825608917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12147138139208291217072611 18220707208812436825608917)
                  ·
                    refine ⟨427047825206541488100209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18220707208812436825608917 427047825206541488100209)
                    ·
                      rfl

theorem cell23_2495018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2495018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495018 prefixEnd_2495018 := by exact prefixLift 2495018
  have htrace : WordTrace (prefixWord ++ tailWord_2495018) baseStart_2495018 baseEnd_2495018 := by
    simpa [prefixWord, tailWord_2495018, baseEnd_2495018] using wordTrace_append hprefix tailTrace_2495018
  have hstable : (prefixWord ++ tailWord_2495018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495018).length < 2 ^ (prefixWord ++ tailWord_2495018).sum := by decide
  have hdescent : baseEnd_2495018 < baseStart_2495018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495022 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_2495022 : Nat := 118140960795 + 2495022 * 2 ^ 59
def prefixEnd_2495022 : Nat := 4983230072969 + 3 ^ 40 * 2495022 * 2
def baseEnd_2495022 : Nat := 142349503282471383183401

theorem tailTrace_2495022 : CollatzResearch.WordTrace tailWord_2495022 prefixEnd_2495022 142349503282471383183401 := by
  unfold tailWord_2495022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375116045871110584736915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60667285577979256451930213 11375116045871110584736915)
  ·
    refine ⟨17062674068806665877105373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11375116045871110584736915 17062674068806665877105373)
    ·
      refine ⟨6398502775802499703914515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17062674068806665877105373 6398502775802499703914515)
      ·
        refine ⟨9597754163703749555871773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398502775802499703914515 9597754163703749555871773)
        ·
          refine ⟨3599157811388906083451915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9597754163703749555871773 3599157811388906083451915)
          ·
            refine ⟨5398736717083359125177873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599157811388906083451915 5398736717083359125177873)
            ·
              refine ⟨4049052537812519343883405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398736717083359125177873 4049052537812519343883405)
              ·
                refine ⟨1518394701679694753956277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4049052537812519343883405 1518394701679694753956277)
                ·
                  refine ⟨142349503282471383183401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1518394701679694753956277 142349503282471383183401)
                  ·
                    rfl

theorem cell23_2495022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_2495022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495022 prefixEnd_2495022 := by exact prefixLift 2495022
  have htrace : WordTrace (prefixWord ++ tailWord_2495022) baseStart_2495022 baseEnd_2495022 := by
    simpa [prefixWord, tailWord_2495022, baseEnd_2495022] using wordTrace_append hprefix tailTrace_2495022
  have hstable : (prefixWord ++ tailWord_2495022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495022).length < 2 ^ (prefixWord ++ tailWord_2495022).sum := by decide
  have hdescent : baseEnd_2495022 < baseStart_2495022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495058 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_2495058 : Nat := 118140960795 + 2495058 * 2 ^ 59
def prefixEnd_2495058 : Nat := 4983230072969 + 3 ^ 40 * 2495058 * 2
def baseEnd_2495058 : Nat := 1281164014845804307800443

theorem tailTrace_2495058 : CollatzResearch.WordTrace tailWord_2495058 prefixEnd_2495058 1281164014845804307800443 := by
  unfold tailWord_2495058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22750560348709615706551457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60668160929892308550803885 22750560348709615706551457)
  ·
    refine ⟨17062920261532211779913593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22750560348709615706551457 17062920261532211779913593)
    ·
      refine ⟨12797190196149158834935195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17062920261532211779913593 12797190196149158834935195)
      ·
        refine ⟨19195785294223738252402793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12797190196149158834935195 19195785294223738252402793)
        ·
          refine ⟨14396838970667803689302095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19195785294223738252402793 14396838970667803689302095)
          ·
            refine ⟨21595258456001705533953143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14396838970667803689302095 21595258456001705533953143)
            ·
              refine ⟨32392887684002558300929715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21595258456001705533953143 32392887684002558300929715)
              ·
                refine ⟨48589331526003837451394573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32392887684002558300929715 48589331526003837451394573)
                ·
                  refine ⟨18220999322251439044272965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48589331526003837451394573 18220999322251439044272965)
                  ·
                    refine ⟨3416437372922144820801181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18220999322251439044272965 3416437372922144820801181)
                    ·
                      refine ⟨1281164014845804307800443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3416437372922144820801181 1281164014845804307800443)
                      ·
                        rfl

theorem cell23_2495058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_2495058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495058 prefixEnd_2495058 := by exact prefixLift 2495058
  have htrace : WordTrace (prefixWord ++ tailWord_2495058) baseStart_2495058 baseEnd_2495058 := by
    simpa [prefixWord, tailWord_2495058, baseEnd_2495058] using wordTrace_append hprefix tailTrace_2495058
  have hstable : (prefixWord ++ tailWord_2495058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495058).length < 2 ^ (prefixWord ++ tailWord_2495058).sum := by decide
  have hdescent : baseEnd_2495058 < baseStart_2495058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495132 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2495132 : Nat := 118140960795 + 2495132 * 2 ^ 59
def prefixEnd_2495132 : Nat := 4983230072969 + 3 ^ 40 * 2495132 * 2
def baseEnd_2495132 : Nat := 1281202012414237018275103

theorem tailTrace_2495132 : CollatzResearch.WordTrace tailWord_2495132 prefixEnd_2495132 1281202012414237018275103 := by
  unfold tailWord_2495132
  simp only [CollatzResearch.WordTrace]
  refine ⟨45502470198285186732199825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60669960264380248976266433 45502470198285186732199825)
  ·
    refine ⟨34126852648713890049149869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45502470198285186732199825 34126852648713890049149869)
    ·
      refine ⟨12797569743267708768431201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34126852648713890049149869 12797569743267708768431201)
      ·
        refine ⟨9598177307450781576323401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12797569743267708768431201 9598177307450781576323401)
        ·
          refine ⟨7198632980588086182242551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9598177307450781576323401 7198632980588086182242551)
          ·
            refine ⟨10797949470882129273363827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198632980588086182242551 10797949470882129273363827)
            ·
              refine ⟨16196924206323193910045741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10797949470882129273363827 16196924206323193910045741)
              ·
                refine ⟨6073846577371197716267153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16196924206323193910045741 6073846577371197716267153)
                ·
                  refine ⟨4555384933028398287200365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6073846577371197716267153 4555384933028398287200365)
                  ·
                    refine ⟨1708269349885649357700137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4555384933028398287200365 1708269349885649357700137)
                    ·
                      refine ⟨1281202012414237018275103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708269349885649357700137 1281202012414237018275103)
                      ·
                        rfl

theorem cell23_2495132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2495132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495132 prefixEnd_2495132 := by exact prefixLift 2495132
  have htrace : WordTrace (prefixWord ++ tailWord_2495132) baseStart_2495132 baseEnd_2495132 := by
    simpa [prefixWord, tailWord_2495132, baseEnd_2495132] using wordTrace_append hprefix tailTrace_2495132
  have hstable : (prefixWord ++ tailWord_2495132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495132).length < 2 ^ (prefixWord ++ tailWord_2495132).sum := by decide
  have hdescent : baseEnd_2495132 < baseStart_2495132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
