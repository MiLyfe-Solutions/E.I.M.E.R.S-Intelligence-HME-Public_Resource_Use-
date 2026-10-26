import V185TrunkScan22Chunk003

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_35603 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_35603 : Nat := 118140960795 + 35603 * 2 ^ 59
def prefixEnd_35603 : Nat := 4983230072969 + 3 ^ 40 * 35603 * 2
def baseEnd_35603 : Nat := 12187634494752957865847

theorem tailTrace_35603 : CollatzResearch.WordTrace tailWord_35603 prefixEnd_35603 12187634494752957865847 := by
  unfold tailWord_35603
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298548090023886353415463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 865698726682590902276975 1298548090023886353415463)
  ·
    refine ⟨1947822135035829530123195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1298548090023886353415463 1947822135035829530123195)
    ·
      refine ⟨2921733202553744295184793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947822135035829530123195 2921733202553744295184793)
      ·
        refine ⟨2191299901915308221388595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921733202553744295184793 2191299901915308221388595)
        ·
          refine ⟨3286949852872962332082893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191299901915308221388595 3286949852872962332082893)
          ·
            refine ⟨1232606194827360874531085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3286949852872962332082893 1232606194827360874531085)
            ·
              refine ⟨462227323060260327949157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1232606194827360874531085 462227323060260327949157)
              ·
                refine ⟨86667623073798811490467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 462227323060260327949157 86667623073798811490467)
                ·
                  refine ⟨130001434610698217235701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86667623073798811490467 130001434610698217235701)
                  ·
                    refine ⟨12187634494752957865847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 130001434610698217235701 12187634494752957865847)
                    ·
                      rfl

theorem cell22_35603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_35603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35603 prefixEnd_35603 := by exact prefixLift 35603
  have htrace : WordTrace (prefixWord ++ tailWord_35603) baseStart_35603 baseEnd_35603 := by
    simpa [prefixWord, tailWord_35603, baseEnd_35603] using wordTrace_append hprefix tailTrace_35603
  have hstable : (prefixWord ++ tailWord_35603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35603).length < 2 ^ (prefixWord ++ tailWord_35603).sum := by decide
  have hdescent : baseEnd_35603 < baseStart_35603 := by decide
  rcases family_descends (prefixWord ++ tailWord_35603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35607 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 1, 4]
def baseStart_35607 : Nat := 118140960795 + 35607 * 2 ^ 59
def prefixEnd_35607 : Nat := 4983230072969 + 3 ^ 40 * 35607 * 2
def baseEnd_35607 : Nat := 12189003776498280765835

theorem tailTrace_35607 : CollatzResearch.WordTrace tailWord_35607 prefixEnd_35607 12189003776498280765835 := by
  unfold tailWord_35607
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298693982009395036561075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 865795988006263357707383 1298693982009395036561075)
  ·
    refine ⟨1948040973014092554841613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1298693982009395036561075 1948040973014092554841613)
    ·
      refine ⟨730515364880284708065605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1948040973014092554841613 730515364880284708065605)
      ·
        refine ⟨136971630915053382762301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 730515364880284708065605 136971630915053382762301)
        ·
          refine ⟨51364361593145018535863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136971630915053382762301 51364361593145018535863)
          ·
            refine ⟨77046542389717527803795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51364361593145018535863 77046542389717527803795)
            ·
              refine ⟨115569813584576291705693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77046542389717527803795 115569813584576291705693)
              ·
                refine ⟨43338680094216109389635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115569813584576291705693 43338680094216109389635)
                ·
                  refine ⟨65008020141324164084453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43338680094216109389635 65008020141324164084453)
                  ·
                    refine ⟨12189003776498280765835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65008020141324164084453 12189003776498280765835)
                    ·
                      rfl

theorem cell22_35607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_35607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35607 prefixEnd_35607 := by exact prefixLift 35607
  have htrace : WordTrace (prefixWord ++ tailWord_35607) baseStart_35607 baseEnd_35607 := by
    simpa [prefixWord, tailWord_35607, baseEnd_35607] using wordTrace_append hprefix tailTrace_35607
  have hstable : (prefixWord ++ tailWord_35607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35607).length < 2 ^ (prefixWord ++ tailWord_35607).sum := by decide
  have hdescent : baseEnd_35607 < baseStart_35607 := by decide
  rcases family_descends (prefixWord ++ tailWord_35607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35633 : List Nat := [1, 2, 2, 3, 2, 1, 2, 9]
def baseStart_35633 : Nat := 118140960795 + 35633 * 2 ^ 59
def prefixEnd_35633 : Nat := 4983230072969 + 3 ^ 40 * 35633 * 2
def baseEnd_35633 : Nat := 1355322678649208846195

theorem tailTrace_35633 : CollatzResearch.WordTrace tailWord_35633 prefixEnd_35633 1355322678649208846195 := by
  unfold tailWord_35633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299642279915201477007553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 866428186610134318005035 1299642279915201477007553)
  ·
    refine ⟨974731709936401107755665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1299642279915201477007553 974731709936401107755665)
    ·
      refine ⟨731048782452300830816749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 974731709936401107755665 731048782452300830816749)
      ·
        refine ⟨274143293419612811556281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 731048782452300830816749 274143293419612811556281)
        ·
          refine ⟨205607470064709608667211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274143293419612811556281 205607470064709608667211)
          ·
            refine ⟨308411205097064413000817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205607470064709608667211 308411205097064413000817)
            ·
              refine ⟨231308403822798309750613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308411205097064413000817 231308403822798309750613)
              ·
                refine ⟨1355322678649208846195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 231308403822798309750613 1355322678649208846195)
                ·
                  rfl

theorem cell22_35633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 9].length) (baseStart_35633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35633 prefixEnd_35633 := by exact prefixLift 35633
  have htrace : WordTrace (prefixWord ++ tailWord_35633) baseStart_35633 baseEnd_35633 := by
    simpa [prefixWord, tailWord_35633, baseEnd_35633] using wordTrace_append hprefix tailTrace_35633
  have hstable : (prefixWord ++ tailWord_35633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35633).length < 2 ^ (prefixWord ++ tailWord_35633).sum := by decide
  have hdescent : baseEnd_35633 < baseStart_35633 := by decide
  rcases family_descends (prefixWord ++ tailWord_35633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35637 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_35637 : Nat := 118140960795 + 35637 * 2 ^ 59
def prefixEnd_35637 : Nat := 4983230072969 + 3 ^ 40 * 35637 * 2
def baseEnd_35637 : Nat := 12199273389588202515743

theorem tailTrace_35637 : CollatzResearch.WordTrace tailWord_35637 prefixEnd_35637 12199273389588202515743 := by
  unfold tailWord_35637
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299788171900710160153165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 866525447933806773435443 1299788171900710160153165)
  ·
    refine ⟨487420564462766310057437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1299788171900710160153165 487420564462766310057437)
    ·
      refine ⟨182782711673537366271539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 487420564462766310057437 182782711673537366271539)
      ·
        refine ⟨274174067510306049407309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182782711673537366271539 274174067510306049407309)
        ·
          refine ⟨102815275316364768527741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274174067510306049407309 102815275316364768527741)
          ·
            refine ⟨38555728243636788197903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102815275316364768527741 38555728243636788197903)
            ·
              refine ⟨57833592365455182296855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38555728243636788197903 57833592365455182296855)
              ·
                refine ⟨86750388548182773445283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57833592365455182296855 86750388548182773445283)
                ·
                  refine ⟨130125582822274160167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86750388548182773445283 130125582822274160167925)
                  ·
                    refine ⟨12199273389588202515743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 130125582822274160167925 12199273389588202515743)
                    ·
                      rfl

theorem cell22_35637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_35637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35637 prefixEnd_35637 := by exact prefixLift 35637
  have htrace : WordTrace (prefixWord ++ tailWord_35637) baseStart_35637 baseEnd_35637 := by
    simpa [prefixWord, tailWord_35637, baseEnd_35637] using wordTrace_append hprefix tailTrace_35637
  have hstable : (prefixWord ++ tailWord_35637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35637).length < 2 ^ (prefixWord ++ tailWord_35637).sum := by decide
  have hdescent : baseEnd_35637 < baseStart_35637 := by decide
  rcases family_descends (prefixWord ++ tailWord_35637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35770 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_35770 : Nat := 118140960795 + 35770 * 2 ^ 59
def prefixEnd_35770 : Nat := 4983230072969 + 3 ^ 40 * 35770 * 2
def baseEnd_35770 : Nat := 12244802007620188940335

theorem tailTrace_35770 : CollatzResearch.WordTrace tailWord_35770 prefixEnd_35770 12244802007620188940335 := by
  unfold tailWord_35770
  simp only [CollatzResearch.WordTrace]
  refine ⟨326159770104718468686191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 869759386945915916496509 326159770104718468686191)
  ·
    refine ⟨489239655157077703029287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326159770104718468686191 489239655157077703029287)
    ·
      refine ⟨733859482735616554543931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489239655157077703029287 733859482735616554543931)
      ·
        refine ⟨1100789224103424831815897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733859482735616554543931 1100789224103424831815897)
        ·
          refine ⟨825591918077568623861923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100789224103424831815897 825591918077568623861923)
          ·
            refine ⟨1238387877116352935792885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825591918077568623861923 1238387877116352935792885)
            ·
              refine ⟨116098863479658087730583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1238387877116352935792885 116098863479658087730583)
              ·
                refine ⟨174148295219487131595875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116098863479658087730583 174148295219487131595875)
                ·
                  refine ⟨261222442829230697393813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174148295219487131595875 261222442829230697393813)
                  ·
                    refine ⟨12244802007620188940335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 261222442829230697393813 12244802007620188940335)
                    ·
                      rfl

theorem cell22_35770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_35770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35770 prefixEnd_35770 := by exact prefixLift 35770
  have htrace : WordTrace (prefixWord ++ tailWord_35770) baseStart_35770 baseEnd_35770 := by
    simpa [prefixWord, tailWord_35770, baseEnd_35770] using wordTrace_append hprefix tailTrace_35770
  have hstable : (prefixWord ++ tailWord_35770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35770).length < 2 ^ (prefixWord ++ tailWord_35770).sum := by decide
  have hdescent : baseEnd_35770 < baseStart_35770 := by decide
  rcases family_descends (prefixWord ++ tailWord_35770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35774 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_35774 : Nat := 118140960795 + 35774 * 2 ^ 59
def prefixEnd_35774 : Nat := 4983230072969 + 3 ^ 40 * 35774 * 2
def baseEnd_35774 : Nat := 4082057096455170613441

theorem tailTrace_35774 : CollatzResearch.WordTrace tailWord_35774 prefixEnd_35774 4082057096455170613441 := by
  unfold tailWord_35774
  simp only [CollatzResearch.WordTrace]
  refine ⟨163098121550547819736297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 869856648269588371926917 163098121550547819736297)
  ·
    refine ⟨122323591162910864802223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163098121550547819736297 122323591162910864802223)
    ·
      refine ⟨183485386744366297203335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122323591162910864802223 183485386744366297203335)
      ·
        refine ⟨275228080116549445805003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183485386744366297203335 275228080116549445805003)
        ·
          refine ⟨412842120174824168707505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275228080116549445805003 412842120174824168707505)
          ·
            refine ⟨309631590131118126530629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412842120174824168707505 309631590131118126530629)
            ·
              refine ⟨58055923149584648724493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309631590131118126530629 58055923149584648724493)
              ·
                refine ⟨21770971181094243271685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58055923149584648724493 21770971181094243271685)
                ·
                  refine ⟨4082057096455170613441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21770971181094243271685 4082057096455170613441)
                  ·
                    rfl

theorem cell22_35774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_35774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35774 prefixEnd_35774 := by exact prefixLift 35774
  have htrace : WordTrace (prefixWord ++ tailWord_35774) baseStart_35774 baseEnd_35774 := by
    simpa [prefixWord, tailWord_35774, baseEnd_35774] using wordTrace_append hprefix tailTrace_35774
  have hstable : (prefixWord ++ tailWord_35774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35774).length < 2 ^ (prefixWord ++ tailWord_35774).sum := by decide
  have hdescent : baseEnd_35774 < baseStart_35774 := by decide
  rcases family_descends (prefixWord ++ tailWord_35774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35847 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 5]
def baseStart_35847 : Nat := 118140960795 + 35847 * 2 ^ 59
def prefixEnd_35847 : Nat := 4983230072969 + 3 ^ 40 * 35847 * 2
def baseEnd_35847 : Nat := 4090386893739218255033

theorem tailTrace_35847 : CollatzResearch.WordTrace tailWord_35847 prefixEnd_35847 4090386893739218255033 := by
  unfold tailWord_35847
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307447501139916025297795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 871631667426610683531863 1307447501139916025297795)
  ·
    refine ⟨1961171251709874037946693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1307447501139916025297795 1961171251709874037946693)
    ·
      refine ⟨367719609695601382115005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1961171251709874037946693 367719609695601382115005)
      ·
        refine ⟨137894853635850518293127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367719609695601382115005 137894853635850518293127)
        ·
          refine ⟨206842280453775777439691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137894853635850518293127 206842280453775777439691)
          ·
            refine ⟨310263420680663666159537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206842280453775777439691 310263420680663666159537)
            ·
              refine ⟨232697565510497749619653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310263420680663666159537 232697565510497749619653)
              ·
                refine ⟨43630793533218328053685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232697565510497749619653 43630793533218328053685)
                ·
                  refine ⟨4090386893739218255033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43630793533218328053685 4090386893739218255033)
                  ·
                    rfl

theorem cell22_35847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 5].length) (baseStart_35847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35847 prefixEnd_35847 := by exact prefixLift 35847
  have htrace : WordTrace (prefixWord ++ tailWord_35847) baseStart_35847 baseEnd_35847 := by
    simpa [prefixWord, tailWord_35847, baseEnd_35847] using wordTrace_append hprefix tailTrace_35847
  have hstable : (prefixWord ++ tailWord_35847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35847).length < 2 ^ (prefixWord ++ tailWord_35847).sum := by decide
  have hdescent : baseEnd_35847 < baseStart_35847 := by decide
  rcases family_descends (prefixWord ++ tailWord_35847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35864 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_35864 : Nat := 118140960795 + 35864 * 2 ^ 59
def prefixEnd_35864 : Nat := 4983230072969 + 3 ^ 40 * 35864 * 2
def baseEnd_35864 : Nat := 4092326709545092363349

theorem tailTrace_35864 : CollatzResearch.WordTrace tailWord_35864 prefixEnd_35864 4092326709545092363349 := by
  unfold tailWord_35864
  simp only [CollatzResearch.WordTrace]
  refine ⟨654033771039163964333323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 872045028052218619111097 654033771039163964333323)
  ·
    refine ⟨981050656558745946499985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654033771039163964333323 981050656558745946499985)
    ·
      refine ⟨735787992419059459874989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981050656558745946499985 735787992419059459874989)
      ·
        refine ⟨275920497157147297453121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 735787992419059459874989 275920497157147297453121)
        ·
          refine ⟨206940372867860473089841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275920497157147297453121 206940372867860473089841)
          ·
            refine ⟨155205279650895354817381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206940372867860473089841 155205279650895354817381)
            ·
              refine ⟨29100989934542879028259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155205279650895354817381 29100989934542879028259)
              ·
                refine ⟨43651484901814318542389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29100989934542879028259 43651484901814318542389)
                ·
                  refine ⟨4092326709545092363349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43651484901814318542389 4092326709545092363349)
                  ·
                    rfl

theorem cell22_35864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_35864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35864 prefixEnd_35864 := by exact prefixLift 35864
  have htrace : WordTrace (prefixWord ++ tailWord_35864) baseStart_35864 baseEnd_35864 := by
    simpa [prefixWord, tailWord_35864, baseEnd_35864] using wordTrace_append hprefix tailTrace_35864
  have hstable : (prefixWord ++ tailWord_35864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35864).length < 2 ^ (prefixWord ++ tailWord_35864).sum := by decide
  have hdescent : baseEnd_35864 < baseStart_35864 := by decide
  rcases family_descends (prefixWord ++ tailWord_35864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35877 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_35877 : Nat := 118140960795 + 35877 * 2 ^ 59
def prefixEnd_35877 : Nat := 4983230072969 + 3 ^ 40 * 35877 * 2
def baseEnd_35877 : Nat := 12281430294307576515007

theorem tailTrace_35877 : CollatzResearch.WordTrace tailWord_35877 prefixEnd_35877 12281430294307576515007 := by
  unfold tailWord_35877
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308541691031231148889885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 872361127354154099259923 1308541691031231148889885)
  ·
    refine ⟨490703134136711680833707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1308541691031231148889885 490703134136711680833707)
    ·
      refine ⟨736054701205067521250561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490703134136711680833707 736054701205067521250561)
      ·
        refine ⟨552041025903800640937921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 736054701205067521250561 552041025903800640937921)
        ·
          refine ⟨414030769427850480703441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552041025903800640937921 414030769427850480703441)
          ·
            refine ⟨310523077070887860527581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414030769427850480703441 310523077070887860527581)
            ·
              refine ⟨116446153901582947697843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310523077070887860527581 116446153901582947697843)
              ·
                refine ⟨174669230852374421546765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116446153901582947697843 174669230852374421546765)
                ·
                  refine ⟨65500961569640408080037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174669230852374421546765 65500961569640408080037)
                  ·
                    refine ⟨12281430294307576515007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65500961569640408080037 12281430294307576515007)
                    ·
                      rfl

theorem cell22_35877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_35877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35877 prefixEnd_35877 := by exact prefixLift 35877
  have htrace : WordTrace (prefixWord ++ tailWord_35877) baseStart_35877 baseEnd_35877 := by
    simpa [prefixWord, tailWord_35877, baseEnd_35877] using wordTrace_append hprefix tailTrace_35877
  have hstable : (prefixWord ++ tailWord_35877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35877).length < 2 ^ (prefixWord ++ tailWord_35877).sum := by decide
  have hdescent : baseEnd_35877 < baseStart_35877 := by decide
  rcases family_descends (prefixWord ++ tailWord_35877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35986 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_35986 : Nat := 118140960795 + 35986 * 2 ^ 59
def prefixEnd_35986 : Nat := 4983230072969 + 3 ^ 40 * 35986 * 2
def baseEnd_35986 : Nat := 12318743221867625539673

theorem tailTrace_35986 : CollatzResearch.WordTrace tailWord_35986 prefixEnd_35986 12318743221867625539673 := by
  unfold tailWord_35986
  simp only [CollatzResearch.WordTrace]
  refine ⟨328129311909085691151953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 875011498424228509738541 328129311909085691151953)
  ·
    refine ⟨246096983931814268363965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 328129311909085691151953 246096983931814268363965)
    ·
      refine ⟨92286368974430350636487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246096983931814268363965 92286368974430350636487)
      ·
        refine ⟨138429553461645525954731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92286368974430350636487 138429553461645525954731)
        ·
          refine ⟨207644330192468288932097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138429553461645525954731 207644330192468288932097)
          ·
            refine ⟨155733247644351216699073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207644330192468288932097 155733247644351216699073)
            ·
              refine ⟨116799935733263412524305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155733247644351216699073 116799935733263412524305)
              ·
                refine ⟨87599951799947559393229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116799935733263412524305 87599951799947559393229)
                ·
                  refine ⟨32849981924980334772461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87599951799947559393229 32849981924980334772461)
                  ·
                    refine ⟨12318743221867625539673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32849981924980334772461 12318743221867625539673)
                    ·
                      rfl

theorem cell22_35986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_35986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_35986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_35986 prefixEnd_35986 := by exact prefixLift 35986
  have htrace : WordTrace (prefixWord ++ tailWord_35986) baseStart_35986 baseEnd_35986 := by
    simpa [prefixWord, tailWord_35986, baseEnd_35986] using wordTrace_append hprefix tailTrace_35986
  have hstable : (prefixWord ++ tailWord_35986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35986).length < 2 ^ (prefixWord ++ tailWord_35986).sum := by decide
  have hdescent : baseEnd_35986 < baseStart_35986 := by decide
  rcases family_descends (prefixWord ++ tailWord_35986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36027 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 6]
def baseStart_36027 : Nat := 118140960795 + 36027 * 2 ^ 59
def prefixEnd_36027 : Nat := 4983230072969 + 3 ^ 40 * 36027 * 2
def baseEnd_36027 : Nat := 4110926119919061754849

theorem tailTrace_36027 : CollatzResearch.WordTrace tailWord_36027 prefixEnd_36027 4110926119919061754849 := by
  unfold tailWord_36027
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314012640487806766850335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 876008426991871177900223 1314012640487806766850335)
  ·
    refine ⟨1971018960731710150275503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314012640487806766850335 1971018960731710150275503)
    ·
      refine ⟨2956528441097565225413255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971018960731710150275503 2956528441097565225413255)
      ·
        refine ⟨4434792661646347838119883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956528441097565225413255 4434792661646347838119883)
        ·
          refine ⟨6652188992469521757179825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4434792661646347838119883 6652188992469521757179825)
          ·
            refine ⟨4989141744352141317884869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6652188992469521757179825 4989141744352141317884869)
            ·
              refine ⟨935464077066026497103413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4989141744352141317884869 935464077066026497103413)
              ·
                refine ⟨87699757224939984103445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935464077066026497103413 87699757224939984103445)
                ·
                  refine ⟨4110926119919061754849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87699757224939984103445 4110926119919061754849)
                  ·
                    rfl

theorem cell22_36027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_36027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36027 prefixEnd_36027 := by exact prefixLift 36027
  have htrace : WordTrace (prefixWord ++ tailWord_36027) baseStart_36027 baseEnd_36027 := by
    simpa [prefixWord, tailWord_36027, baseEnd_36027] using wordTrace_append hprefix tailTrace_36027
  have hstable : (prefixWord ++ tailWord_36027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36027).length < 2 ^ (prefixWord ++ tailWord_36027).sum := by decide
  have hdescent : baseEnd_36027 < baseStart_36027 := by decide
  rcases family_descends (prefixWord ++ tailWord_36027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36033 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 5]
def baseStart_36033 : Nat := 118140960795 + 36033 * 2 ^ 59
def prefixEnd_36033 : Nat := 4983230072969 + 3 ^ 40 * 36033 * 2
def baseEnd_36033 : Nat := 4111610760791723204843

theorem tailTrace_36033 : CollatzResearch.WordTrace tailWord_36033 prefixEnd_36033 4111610760791723204843 := by
  unfold tailWord_36033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314231478466069791568753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 876154318977379861045835 1314231478466069791568753)
  ·
    refine ⟨985673608849552343676565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1314231478466069791568753 985673608849552343676565)
    ·
      refine ⟨46203450414822766109839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 985673608849552343676565 46203450414822766109839)
      ·
        refine ⟨69305175622234149164759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46203450414822766109839 69305175622234149164759)
        ·
          refine ⟨103957763433351223747139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69305175622234149164759 103957763433351223747139)
          ·
            refine ⟨155936645150026835620709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103957763433351223747139 155936645150026835620709)
            ·
              refine ⟨29238120965630031678883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155936645150026835620709 29238120965630031678883)
              ·
                refine ⟨43857181448445047518325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29238120965630031678883 43857181448445047518325)
                ·
                  refine ⟨4111610760791723204843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43857181448445047518325 4111610760791723204843)
                  ·
                    rfl

theorem cell22_36033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_36033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36033 prefixEnd_36033 := by exact prefixLift 36033
  have htrace : WordTrace (prefixWord ++ tailWord_36033) baseStart_36033 baseEnd_36033 := by
    simpa [prefixWord, tailWord_36033, baseEnd_36033] using wordTrace_append hprefix tailTrace_36033
  have hstable : (prefixWord ++ tailWord_36033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36033).length < 2 ^ (prefixWord ++ tailWord_36033).sum := by decide
  have hdescent : baseEnd_36033 < baseStart_36033 := by decide
  rcases family_descends (prefixWord ++ tailWord_36033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36046 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_36046 : Nat := 118140960795 + 36046 * 2 ^ 59
def prefixEnd_36046 : Nat := 4983230072969 + 3 ^ 40 * 36046 * 2
def baseEnd_36046 : Nat := 12339282448047469039489

theorem tailTrace_36046 : CollatzResearch.WordTrace tailWord_36046 prefixEnd_36046 12339282448047469039489 := by
  unfold tailWord_36046
  simp only [CollatzResearch.WordTrace]
  refine ⟨164338203427371626473999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 876470418279315341194661 164338203427371626473999)
  ·
    refine ⟨246507305141057439710999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164338203427371626473999 246507305141057439710999)
    ·
      refine ⟨369760957711586159566499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246507305141057439710999 369760957711586159566499)
      ·
        refine ⟨554641436567379239349749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369760957711586159566499 554641436567379239349749)
        ·
          refine ⟨51997634678191803689039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 554641436567379239349749 51997634678191803689039)
          ·
            refine ⟨77996452017287705533559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51997634678191803689039 77996452017287705533559)
            ·
              refine ⟨116994678025931558300339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77996452017287705533559 116994678025931558300339)
              ·
                refine ⟨175492017038897337450509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116994678025931558300339 175492017038897337450509)
                ·
                  refine ⟨65809506389586501543941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175492017038897337450509 65809506389586501543941)
                  ·
                    refine ⟨12339282448047469039489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65809506389586501543941 12339282448047469039489)
                    ·
                      rfl

theorem cell22_36046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_36046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36046 prefixEnd_36046 := by exact prefixLift 36046
  have htrace : WordTrace (prefixWord ++ tailWord_36046) baseStart_36046 baseEnd_36046 := by
    simpa [prefixWord, tailWord_36046, baseEnd_36046] using wordTrace_append hprefix tailTrace_36046
  have hstable : (prefixWord ++ tailWord_36046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36046).length < 2 ^ (prefixWord ++ tailWord_36046).sum := by decide
  have hdescent : baseEnd_36046 < baseStart_36046 := by decide
  rcases family_descends (prefixWord ++ tailWord_36046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36076 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_36076 : Nat := 118140960795 + 36076 * 2 ^ 59
def prefixEnd_36076 : Nat := 4983230072969 + 3 ^ 40 * 36076 * 2
def baseEnd_36076 : Nat := 12349552061137390789397

theorem tailTrace_36076 : CollatzResearch.WordTrace tailWord_36076 prefixEnd_36076 12349552061137390789397 := by
  unfold tailWord_36076
  simp only [CollatzResearch.WordTrace]
  refine ⟨657899908655144067692041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 877199878206858756922721 657899908655144067692041)
  ·
    refine ⟨493424931491358050769031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 657899908655144067692041 493424931491358050769031)
    ·
      refine ⟨740137397237037076153547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493424931491358050769031 740137397237037076153547)
      ·
        refine ⟨1110206095855555614230321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740137397237037076153547 1110206095855555614230321)
        ·
          refine ⟨832654571891666710672741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110206095855555614230321 832654571891666710672741)
          ·
            refine ⟨156122732229687508251139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 832654571891666710672741 156122732229687508251139)
            ·
              refine ⟨234184098344531262376709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156122732229687508251139 234184098344531262376709)
              ·
                refine ⟨43909518439599611695633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234184098344531262376709 43909518439599611695633)
                ·
                  refine ⟨32932138829699708771725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43909518439599611695633 32932138829699708771725)
                  ·
                    refine ⟨12349552061137390789397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32932138829699708771725 12349552061137390789397)
                    ·
                      rfl

theorem cell22_36076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_36076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36076 prefixEnd_36076 := by exact prefixLift 36076
  have htrace : WordTrace (prefixWord ++ tailWord_36076) baseStart_36076 baseEnd_36076 := by
    simpa [prefixWord, tailWord_36076, baseEnd_36076] using wordTrace_append hprefix tailTrace_36076
  have hstable : (prefixWord ++ tailWord_36076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36076).length < 2 ^ (prefixWord ++ tailWord_36076).sum := by decide
  have hdescent : baseEnd_36076 < baseStart_36076 := by decide
  rcases family_descends (prefixWord ++ tailWord_36076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36078 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_36078 : Nat := 118140960795 + 36078 * 2 ^ 59
def prefixEnd_36078 : Nat := 4983230072969 + 3 ^ 40 * 36078 * 2
def baseEnd_36078 : Nat := 4116745567336684079797

theorem tailTrace_36078 : CollatzResearch.WordTrace tailWord_36078 prefixEnd_36078 4116745567336684079797 := by
  unfold tailWord_36078
  simp only [CollatzResearch.WordTrace]
  refine ⟨164484095412880309619611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 877248508868694984637925 164484095412880309619611)
  ·
    refine ⟨246726143119320464429417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164484095412880309619611 246726143119320464429417)
    ·
      refine ⟨185044607339490348322063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246726143119320464429417 185044607339490348322063)
      ·
        refine ⟨277566911009235522483095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185044607339490348322063 277566911009235522483095)
        ·
          refine ⟨416350366513853283724643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277566911009235522483095 416350366513853283724643)
          ·
            refine ⟨624525549770779925586965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416350366513853283724643 624525549770779925586965)
            ·
              refine ⟨29274635145505309011889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 624525549770779925586965 29274635145505309011889)
              ·
                refine ⟨21955976359128981758917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29274635145505309011889 21955976359128981758917)
                ·
                  refine ⟨4116745567336684079797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21955976359128981758917 4116745567336684079797)
                  ·
                    rfl

theorem cell22_36078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_36078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36078 prefixEnd_36078 := by exact prefixLift 36078
  have htrace : WordTrace (prefixWord ++ tailWord_36078) baseStart_36078 baseEnd_36078 := by
    simpa [prefixWord, tailWord_36078, baseEnd_36078] using wordTrace_append hprefix tailTrace_36078
  have hstable : (prefixWord ++ tailWord_36078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36078).length < 2 ^ (prefixWord ++ tailWord_36078).sum := by decide
  have hdescent : baseEnd_36078 < baseStart_36078 := by decide
  rcases family_descends (prefixWord ++ tailWord_36078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36114 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_36114 : Nat := 118140960795 + 36114 * 2 ^ 59
def prefixEnd_36114 : Nat := 4983230072969 + 3 ^ 40 * 36114 * 2
def baseEnd_36114 : Nat := 12362560237717958339281

theorem tailTrace_36114 : CollatzResearch.WordTrace tailWord_36114 prefixEnd_36114 12362560237717958339281 := by
  unfold tailWord_36114
  simp only [CollatzResearch.WordTrace]
  refine ⟨329296447793155156316849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 878123860781747083511597 329296447793155156316849)
  ·
    refine ⟨246972335844866367237637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 329296447793155156316849 246972335844866367237637)
    ·
      refine ⟨46307312970912443857057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246972335844866367237637 46307312970912443857057)
      ·
        refine ⟨34730484728184332892793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46307312970912443857057 34730484728184332892793)
        ·
          refine ⟨26047863546138249669595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34730484728184332892793 26047863546138249669595)
          ·
            refine ⟨39071795319207374504393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26047863546138249669595 39071795319207374504393)
            ·
              refine ⟨29303846489405530878295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39071795319207374504393 29303846489405530878295)
              ·
                refine ⟨43955769734108296317443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29303846489405530878295 43955769734108296317443)
                ·
                  refine ⟨65933654601162444476165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43955769734108296317443 65933654601162444476165)
                  ·
                    refine ⟨12362560237717958339281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65933654601162444476165 12362560237717958339281)
                    ·
                      rfl

theorem cell22_36114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_36114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36114 prefixEnd_36114 := by exact prefixLift 36114
  have htrace : WordTrace (prefixWord ++ tailWord_36114) baseStart_36114 baseEnd_36114 := by
    simpa [prefixWord, tailWord_36114, baseEnd_36114] using wordTrace_append hprefix tailTrace_36114
  have hstable : (prefixWord ++ tailWord_36114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36114).length < 2 ^ (prefixWord ++ tailWord_36114).sum := by decide
  have hdescent : baseEnd_36114 < baseStart_36114 := by decide
  rcases family_descends (prefixWord ++ tailWord_36114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36138 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_36138 : Nat := 118140960795 + 36138 * 2 ^ 59
def prefixEnd_36138 : Nat := 4983230072969 + 3 ^ 40 * 36138 * 2
def baseEnd_36138 : Nat := 12370775928189895739207

theorem tailTrace_36138 : CollatzResearch.WordTrace tailWord_36138 prefixEnd_36138 12370775928189895739207 := by
  unfold tailWord_36138
  simp only [CollatzResearch.WordTrace]
  refine ⟨329515285771418181035267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 878707428723781816094045 329515285771418181035267)
  ·
    refine ⟨494272928657127271552901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329515285771418181035267 494272928657127271552901)
    ·
      refine ⟨92676174123211363416169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 494272928657127271552901 92676174123211363416169)
      ·
        refine ⟨69507130592408522562127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92676174123211363416169 69507130592408522562127)
        ·
          refine ⟨104260695888612783843191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69507130592408522562127 104260695888612783843191)
          ·
            refine ⟨156391043832919175764787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104260695888612783843191 156391043832919175764787)
            ·
              refine ⟨234586565749378763647181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156391043832919175764787 234586565749378763647181)
              ·
                refine ⟨87969962156017036367693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234586565749378763647181 87969962156017036367693)
                ·
                  refine ⟨32988735808506388637885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87969962156017036367693 32988735808506388637885)
                  ·
                    refine ⟨12370775928189895739207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32988735808506388637885 12370775928189895739207)
                    ·
                      rfl

theorem cell22_36138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_36138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36138 prefixEnd_36138 := by exact prefixLift 36138
  have htrace : WordTrace (prefixWord ++ tailWord_36138) baseStart_36138 baseEnd_36138 := by
    simpa [prefixWord, tailWord_36138, baseEnd_36138] using wordTrace_append hprefix tailTrace_36138
  have hstable : (prefixWord ++ tailWord_36138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36138).length < 2 ^ (prefixWord ++ tailWord_36138).sum := by decide
  have hdescent : baseEnd_36138 < baseStart_36138 := by decide
  rcases family_descends (prefixWord ++ tailWord_36138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36189 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_36189 : Nat := 118140960795 + 36189 * 2 ^ 59
def prefixEnd_36189 : Nat := 4983230072969 + 3 ^ 40 * 36189 * 2
def baseEnd_36189 : Nat := 12388234270442762714051

theorem tailTrace_36189 : CollatzResearch.WordTrace tailWord_36189 prefixEnd_36189 12388234270442762714051 := by
  unfold tailWord_36189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319921265900908434247621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 879947510600605622831747 1319921265900908434247621)
  ·
    refine ⟨247485237356420331421429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1319921265900908434247621 247485237356420331421429)
    ·
      refine ⟨23201741002164406070759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 247485237356420331421429 23201741002164406070759)
      ·
        refine ⟨34802611503246609106139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23201741002164406070759 34802611503246609106139)
        ·
          refine ⟨52203917254869913659209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34802611503246609106139 52203917254869913659209)
          ·
            refine ⟨39152937941152435244407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52203917254869913659209 39152937941152435244407)
            ·
              refine ⟨58729406911728652866611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39152937941152435244407 58729406911728652866611)
              ·
                refine ⟨88094110367592979299917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58729406911728652866611 88094110367592979299917)
                ·
                  refine ⟨33035291387847367237469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88094110367592979299917 33035291387847367237469)
                  ·
                    refine ⟨12388234270442762714051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33035291387847367237469 12388234270442762714051)
                    ·
                      rfl

theorem cell22_36189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_36189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36189 prefixEnd_36189 := by exact prefixLift 36189
  have htrace : WordTrace (prefixWord ++ tailWord_36189) baseStart_36189 baseEnd_36189 := by
    simpa [prefixWord, tailWord_36189, baseEnd_36189] using wordTrace_append hprefix tailTrace_36189
  have hstable : (prefixWord ++ tailWord_36189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36189).length < 2 ^ (prefixWord ++ tailWord_36189).sum := by decide
  have hdescent : baseEnd_36189 < baseStart_36189 := by decide
  rcases family_descends (prefixWord ++ tailWord_36189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36196 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_36196 : Nat := 118140960795 + 36196 * 2 ^ 59
def prefixEnd_36196 : Nat := 4983230072969 + 3 ^ 40 * 36196 * 2
def baseEnd_36196 : Nat := 4130210171165692596343

theorem tailTrace_36196 : CollatzResearch.WordTrace tailWord_36196 prefixEnd_36196 4130210171165692596343 := by
  unfold tailWord_36196
  simp only [CollatzResearch.WordTrace]
  refine ⟨660088288437774314876221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 880117717917032419834961 660088288437774314876221)
  ·
    refine ⟨247533108164165368078583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 660088288437774314876221 247533108164165368078583)
    ·
      refine ⟨371299662246248052117875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247533108164165368078583 371299662246248052117875)
      ·
        refine ⟨556949493369372078176813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371299662246248052117875 556949493369372078176813)
        ·
          refine ⟨208856060013514529316305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556949493369372078176813 208856060013514529316305)
          ·
            refine ⟨156642045010135896987229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208856060013514529316305 156642045010135896987229)
            ·
              refine ⟨58740766878800961370211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156642045010135896987229 58740766878800961370211)
              ·
                refine ⟨88111150318201442055317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58740766878800961370211 88111150318201442055317)
                ·
                  refine ⟨4130210171165692596343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88111150318201442055317 4130210171165692596343)
                  ·
                    rfl

theorem cell22_36196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_36196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36196 prefixEnd_36196 := by exact prefixLift 36196
  have htrace : WordTrace (prefixWord ++ tailWord_36196) baseStart_36196 baseEnd_36196 := by
    simpa [prefixWord, tailWord_36196, baseEnd_36196] using wordTrace_append hprefix tailTrace_36196
  have hstable : (prefixWord ++ tailWord_36196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36196).length < 2 ^ (prefixWord ++ tailWord_36196).sum := by decide
  have hdescent : baseEnd_36196 < baseStart_36196 := by decide
  rcases family_descends (prefixWord ++ tailWord_36196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36202 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_36202 : Nat := 118140960795 + 36202 * 2 ^ 59
def prefixEnd_36202 : Nat := 4983230072969 + 3 ^ 40 * 36202 * 2
def baseEnd_36202 : Nat := 4130894812038354046337

theorem tailTrace_36202 : CollatzResearch.WordTrace tailWord_36202 prefixEnd_36202 4130894812038354046337 := by
  unfold tailWord_36202
  simp only [CollatzResearch.WordTrace]
  refine ⟨330098853713452913617715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 880263609902541102980573 330098853713452913617715)
  ·
    refine ⟨495148280570179370426573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 330098853713452913617715 495148280570179370426573)
    ·
      refine ⟨185680605213817263909965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 495148280570179370426573 185680605213817263909965)
      ·
        refine ⟨69630226955181473966237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185680605213817263909965 69630226955181473966237)
        ·
          refine ⟨26111335108193052737339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69630226955181473966237 26111335108193052737339)
          ·
            refine ⟨39167002662289579106009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26111335108193052737339 39167002662289579106009)
            ·
              refine ⟨29375251996717184329507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39167002662289579106009 29375251996717184329507)
              ·
                refine ⟨44062877995075776494261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29375251996717184329507 44062877995075776494261)
                ·
                  refine ⟨4130894812038354046337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44062877995075776494261 4130894812038354046337)
                  ·
                    rfl

theorem cell22_36202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_36202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36202 prefixEnd_36202 := by exact prefixLift 36202
  have htrace : WordTrace (prefixWord ++ tailWord_36202) baseStart_36202 baseEnd_36202 := by
    simpa [prefixWord, tailWord_36202, baseEnd_36202] using wordTrace_append hprefix tailTrace_36202
  have hstable : (prefixWord ++ tailWord_36202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36202).length < 2 ^ (prefixWord ++ tailWord_36202).sum := by decide
  have hdescent : baseEnd_36202 < baseStart_36202 := by decide
  rcases family_descends (prefixWord ++ tailWord_36202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36209 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_36209 : Nat := 118140960795 + 36209 * 2 ^ 59
def prefixEnd_36209 : Nat := 4983230072969 + 3 ^ 40 * 36209 * 2
def baseEnd_36209 : Nat := 12395080679169377213989

theorem tailTrace_36209 : CollatzResearch.WordTrace tailWord_36209 prefixEnd_36209 12395080679169377213989 := by
  unfold tailWord_36209
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320650725828451849975681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 880433817218967899983787 1320650725828451849975681)
  ·
    refine ⟨990488044371338887481761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1320650725828451849975681 990488044371338887481761)
    ·
      refine ⟨742866033278504165611321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 990488044371338887481761 742866033278504165611321)
      ·
        refine ⟨557149524958878124208491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742866033278504165611321 557149524958878124208491)
        ·
          refine ⟨835724287438317186312737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557149524958878124208491 835724287438317186312737)
          ·
            refine ⟨626793215578737889734553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835724287438317186312737 626793215578737889734553)
            ·
              refine ⟨470094911684053417300915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626793215578737889734553 470094911684053417300915)
              ·
                refine ⟨705142367526080125951373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470094911684053417300915 705142367526080125951373)
                ·
                  refine ⟨264428387822280047231765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705142367526080125951373 264428387822280047231765)
                  ·
                    refine ⟨12395080679169377213989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 264428387822280047231765 12395080679169377213989)
                    ·
                      rfl

theorem cell22_36209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_36209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36209 prefixEnd_36209 := by exact prefixLift 36209
  have htrace : WordTrace (prefixWord ++ tailWord_36209) baseStart_36209 baseEnd_36209 := by
    simpa [prefixWord, tailWord_36209, baseEnd_36209] using wordTrace_append hprefix tailTrace_36209
  have hstable : (prefixWord ++ tailWord_36209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36209).length < 2 ^ (prefixWord ++ tailWord_36209).sum := by decide
  have hdescent : baseEnd_36209 < baseStart_36209 := by decide
  rcases family_descends (prefixWord ++ tailWord_36209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36258 : List Nat := [3, 3, 1, 2, 1, 4, 1, 7]
def baseStart_36258 : Nat := 118140960795 + 36258 * 2 ^ 59
def prefixEnd_36258 : Nat := 4983230072969 + 3 ^ 40 * 36258 * 2
def baseEnd_36258 : Nat := 1379094931172175859871

theorem tailTrace_36258 : CollatzResearch.WordTrace tailWord_36258 prefixEnd_36258 1379094931172175859871 := by
  unfold tailWord_36258
  simp only [CollatzResearch.WordTrace]
  refine ⟨330609475662733304627357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 881625268433955479006285 330609475662733304627357)
  ·
    refine ⟨123978553373524989235259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 330609475662733304627357 123978553373524989235259)
    ·
      refine ⟨185967830060287483852889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123978553373524989235259 185967830060287483852889)
      ·
        refine ⟨139475872545215612889667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185967830060287483852889 139475872545215612889667)
        ·
          refine ⟨209213808817823419334501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139475872545215612889667 209213808817823419334501)
          ·
            refine ⟨39227589153341891125219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209213808817823419334501 39227589153341891125219)
            ·
              refine ⟨58841383730012836687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39227589153341891125219 58841383730012836687829)
              ·
                refine ⟨1379094931172175859871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58841383730012836687829 1379094931172175859871)
                ·
                  rfl

theorem cell22_36258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_36258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36258 prefixEnd_36258 := by exact prefixLift 36258
  have htrace : WordTrace (prefixWord ++ tailWord_36258) baseStart_36258 baseEnd_36258 := by
    simpa [prefixWord, tailWord_36258, baseEnd_36258] using wordTrace_append hprefix tailTrace_36258
  have hstable : (prefixWord ++ tailWord_36258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36258).length < 2 ^ (prefixWord ++ tailWord_36258).sum := by decide
  have hdescent : baseEnd_36258 < baseStart_36258 := by decide
  rcases family_descends (prefixWord ++ tailWord_36258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36273 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_36273 : Nat := 118140960795 + 36273 * 2 ^ 59
def prefixEnd_36273 : Nat := 4983230072969 + 3 ^ 40 * 36273 * 2
def baseEnd_36273 : Nat := 12416989187094543613793

theorem tailTrace_36273 : CollatzResearch.WordTrace tailWord_36273 prefixEnd_36273 12416989187094543613793 := by
  unfold tailWord_36273
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322984997596590780305473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 881989998397727186870315 1322984997596590780305473)
  ·
    refine ⟨992238748197443085229105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1322984997596590780305473 992238748197443085229105)
    ·
      refine ⟨744179061148082313921829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 992238748197443085229105 744179061148082313921829)
      ·
        refine ⟨139533573965265433860343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 744179061148082313921829 139533573965265433860343)
        ·
          refine ⟨209300360947898150790515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139533573965265433860343 209300360947898150790515)
          ·
            refine ⟨313950541421847226185773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209300360947898150790515 313950541421847226185773)
            ·
              refine ⟨117731453033192709819665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 313950541421847226185773 117731453033192709819665)
              ·
                refine ⟨88298589774894532364749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117731453033192709819665 88298589774894532364749)
                ·
                  refine ⟨33111971165585449636781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88298589774894532364749 33111971165585449636781)
                  ·
                    refine ⟨12416989187094543613793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33111971165585449636781 12416989187094543613793)
                    ·
                      rfl

theorem cell22_36273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_36273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36273 prefixEnd_36273 := by exact prefixLift 36273
  have htrace : WordTrace (prefixWord ++ tailWord_36273) baseStart_36273 baseEnd_36273 := by
    simpa [prefixWord, tailWord_36273, baseEnd_36273] using wordTrace_append hprefix tailTrace_36273
  have hstable : (prefixWord ++ tailWord_36273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36273).length < 2 ^ (prefixWord ++ tailWord_36273).sum := by decide
  have hdescent : baseEnd_36273 < baseStart_36273 := by decide
  rcases family_descends (prefixWord ++ tailWord_36273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36286 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_36286 : Nat := 118140960795 + 36286 * 2 ^ 59
def prefixEnd_36286 : Nat := 4983230072969 + 3 ^ 40 * 36286 * 2
def baseEnd_36286 : Nat := 4140479784255614346251

theorem tailTrace_36286 : CollatzResearch.WordTrace tailWord_36286 prefixEnd_36286 4140479784255614346251 := by
  unfold tailWord_36286
  simp only [CollatzResearch.WordTrace]
  refine ⟨165432393318686750066089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 882306097699662667019141 165432393318686750066089)
  ·
    refine ⟨124074294989015062549567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165432393318686750066089 124074294989015062549567)
    ·
      refine ⟨186111442483522593824351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124074294989015062549567 186111442483522593824351)
      ·
        refine ⟨279167163725283890736527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186111442483522593824351 279167163725283890736527)
        ·
          refine ⟨418750745587925836104791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279167163725283890736527 418750745587925836104791)
          ·
            refine ⟨628126118381888754157187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418750745587925836104791 628126118381888754157187)
            ·
              refine ⟨942189177572833131235781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628126118381888754157187 942189177572833131235781)
              ·
                refine ⟨176660470794906212106709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 942189177572833131235781 176660470794906212106709)
                ·
                  refine ⟨4140479784255614346251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 176660470794906212106709 4140479784255614346251)
                  ·
                    rfl

theorem cell22_36286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_36286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36286 prefixEnd_36286 := by exact prefixLift 36286
  have htrace : WordTrace (prefixWord ++ tailWord_36286) baseStart_36286 baseEnd_36286 := by
    simpa [prefixWord, tailWord_36286, baseEnd_36286] using wordTrace_append hprefix tailTrace_36286
  have hstable : (prefixWord ++ tailWord_36286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36286).length < 2 ^ (prefixWord ++ tailWord_36286).sum := by decide
  have hdescent : baseEnd_36286 < baseStart_36286 := by decide
  rcases family_descends (prefixWord ++ tailWord_36286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36346 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_36346 : Nat := 118140960795 + 36346 * 2 ^ 59
def prefixEnd_36346 : Nat := 4983230072969 + 3 ^ 40 * 36346 * 2
def baseEnd_36346 : Nat := 12441978578946686538569

theorem tailTrace_36346 : CollatzResearch.WordTrace tailWord_36346 prefixEnd_36346 12441978578946686538569 := by
  unfold tailWord_36346
  simp only [CollatzResearch.WordTrace]
  refine ⟨331411881583031061928223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 883765017554749498475261 331411881583031061928223)
  ·
    refine ⟨497117822374546592892335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331411881583031061928223 497117822374546592892335)
    ·
      refine ⟨745676733561819889338503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497117822374546592892335 745676733561819889338503)
      ·
        refine ⟨1118515100342729834007755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745676733561819889338503 1118515100342729834007755)
        ·
          refine ⟨1677772650514094751011633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118515100342729834007755 1677772650514094751011633)
          ·
            refine ⟨1258329487885571063258725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1677772650514094751011633 1258329487885571063258725)
            ·
              refine ⟨235936778978544574361011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1258329487885571063258725 235936778978544574361011)
              ·
                refine ⟨353905168467816861541517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235936778978544574361011 353905168467816861541517)
                ·
                  refine ⟨132714438175431323078069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353905168467816861541517 132714438175431323078069)
                  ·
                    refine ⟨12441978578946686538569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132714438175431323078069 12441978578946686538569)
                    ·
                      rfl

theorem cell22_36346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_36346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36346 prefixEnd_36346 := by exact prefixLift 36346
  have htrace : WordTrace (prefixWord ++ tailWord_36346) baseStart_36346 baseEnd_36346 := by
    simpa [prefixWord, tailWord_36346, baseEnd_36346] using wordTrace_append hprefix tailTrace_36346
  have hstable : (prefixWord ++ tailWord_36346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36346).length < 2 ^ (prefixWord ++ tailWord_36346).sum := by decide
  have hdescent : baseEnd_36346 < baseStart_36346 := by decide
  rcases family_descends (prefixWord ++ tailWord_36346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36358 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_36358 : Nat := 118140960795 + 36358 * 2 ^ 59
def prefixEnd_36358 : Nat := 4983230072969 + 3 ^ 40 * 36358 * 2
def baseEnd_36358 : Nat := 12446086424182655238533

theorem tailTrace_36358 : CollatzResearch.WordTrace tailWord_36358 prefixEnd_36358 12446086424182655238533 := by
  unfold tailWord_36358
  simp only [CollatzResearch.WordTrace]
  refine ⟨41440162571520321785929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 884056801525766864766485 41440162571520321785929)
  ·
    refine ⟨31080121928640241339447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41440162571520321785929 31080121928640241339447)
    ·
      refine ⟨46620182892960362009171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31080121928640241339447 46620182892960362009171)
      ·
        refine ⟨69930274339440543013757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46620182892960362009171 69930274339440543013757)
        ·
          refine ⟨26223852877290203630159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69930274339440543013757 26223852877290203630159)
          ·
            refine ⟨39335779315935305445239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26223852877290203630159 39335779315935305445239)
            ·
              refine ⟨59003668973902958167859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39335779315935305445239 59003668973902958167859)
              ·
                refine ⟨88505503460854437251789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59003668973902958167859 88505503460854437251789)
                ·
                  refine ⟨33189563797820413969421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88505503460854437251789 33189563797820413969421)
                  ·
                    refine ⟨12446086424182655238533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33189563797820413969421 12446086424182655238533)
                    ·
                      rfl

theorem cell22_36358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_36358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36358 prefixEnd_36358 := by exact prefixLift 36358
  have htrace : WordTrace (prefixWord ++ tailWord_36358) baseStart_36358 baseEnd_36358 := by
    simpa [prefixWord, tailWord_36358, baseEnd_36358] using wordTrace_append hprefix tailTrace_36358
  have hstable : (prefixWord ++ tailWord_36358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36358).length < 2 ^ (prefixWord ++ tailWord_36358).sum := by decide
  have hdescent : baseEnd_36358 < baseStart_36358 := by decide
  rcases family_descends (prefixWord ++ tailWord_36358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36380 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_36380 : Nat := 118140960795 + 36380 * 2 ^ 59
def prefixEnd_36380 : Nat := 4983230072969 + 3 ^ 40 * 36380 * 2
def baseEnd_36380 : Nat := 12453617473781931188465

theorem tailTrace_36380 : CollatzResearch.WordTrace tailWord_36380 prefixEnd_36380 12453617473781931188465 := by
  unfold tailWord_36380
  simp only [CollatzResearch.WordTrace]
  refine ⟨663443804104474027225297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 884591738805965369633729 663443804104474027225297)
  ·
    refine ⟨497582853078355520418973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 663443804104474027225297 497582853078355520418973)
    ·
      refine ⟨186593569904383320157115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 497582853078355520418973 186593569904383320157115)
      ·
        refine ⟨279890354856574980235673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186593569904383320157115 279890354856574980235673)
        ·
          refine ⟨209917766142431235176755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279890354856574980235673 209917766142431235176755)
          ·
            refine ⟨314876649213646852765133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209917766142431235176755 314876649213646852765133)
            ·
              refine ⟨118078743455117569786925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314876649213646852765133 118078743455117569786925)
              ·
                refine ⟨44279528795669088670097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118078743455117569786925 44279528795669088670097)
                ·
                  refine ⟨33209646596751816502573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44279528795669088670097 33209646596751816502573)
                  ·
                    refine ⟨12453617473781931188465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33209646596751816502573 12453617473781931188465)
                    ·
                      rfl

theorem cell22_36380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_36380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36380 prefixEnd_36380 := by exact prefixLift 36380
  have htrace : WordTrace (prefixWord ++ tailWord_36380) baseStart_36380 baseEnd_36380 := by
    simpa [prefixWord, tailWord_36380, baseEnd_36380] using wordTrace_append hprefix tailTrace_36380
  have hstable : (prefixWord ++ tailWord_36380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36380).length < 2 ^ (prefixWord ++ tailWord_36380).sum := by decide
  have hdescent : baseEnd_36380 < baseStart_36380 := by decide
  rcases family_descends (prefixWord ++ tailWord_36380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36470 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_36470 : Nat := 118140960795 + 36470 * 2 ^ 59
def prefixEnd_36470 : Nat := 4983230072969 + 3 ^ 40 * 36470 * 2
def baseEnd_36470 : Nat := 12484426313051696438189

theorem tailTrace_36470 : CollatzResearch.WordTrace tailWord_36470 prefixEnd_36470 12484426313051696438189 := by
  unfold tailWord_36470
  simp only [CollatzResearch.WordTrace]
  refine ⟨83135636117680839076679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 886780118588595616817909 83135636117680839076679)
  ·
    refine ⟨124703454176521258615019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83135636117680839076679 124703454176521258615019)
    ·
      refine ⟨187055181264781887922529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124703454176521258615019 187055181264781887922529)
      ·
        refine ⟨140291385948586415941897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187055181264781887922529 140291385948586415941897)
        ·
          refine ⟨105218539461439811956423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140291385948586415941897 105218539461439811956423)
          ·
            refine ⟨157827809192159717934635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105218539461439811956423 157827809192159717934635)
            ·
              refine ⟨236741713788239576901953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157827809192159717934635 236741713788239576901953)
              ·
                refine ⟨177556285341179682676465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236741713788239576901953 177556285341179682676465)
                ·
                  refine ⟨133167214005884762007349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177556285341179682676465 133167214005884762007349)
                  ·
                    refine ⟨12484426313051696438189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133167214005884762007349 12484426313051696438189)
                    ·
                      rfl

theorem cell22_36470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_36470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36470 prefixEnd_36470 := by exact prefixLift 36470
  have htrace : WordTrace (prefixWord ++ tailWord_36470) baseStart_36470 baseEnd_36470 := by
    simpa [prefixWord, tailWord_36470, baseEnd_36470] using wordTrace_append hprefix tailTrace_36470
  have hstable : (prefixWord ++ tailWord_36470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36470).length < 2 ^ (prefixWord ++ tailWord_36470).sum := by decide
  have hdescent : baseEnd_36470 < baseStart_36470 := by decide
  rcases family_descends (prefixWord ++ tailWord_36470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36534 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_36534 : Nat := 118140960795 + 36534 * 2 ^ 59
def prefixEnd_36534 : Nat := 4983230072969 + 3 ^ 40 * 36534 * 2
def baseEnd_36534 : Nat := 4168778273658954279331

theorem tailTrace_36534 : CollatzResearch.WordTrace tailWord_36534 prefixEnd_36534 4168778273658954279331 := by
  unfold tailWord_36534
  simp only [CollatzResearch.WordTrace]
  refine ⟨83281528103189522222291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 888336299767354903704437 83281528103189522222291)
  ·
    refine ⟨124922292154784283333437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83281528103189522222291 124922292154784283333437)
    ·
      refine ⟨46845859558044106250039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124922292154784283333437 46845859558044106250039)
      ·
        refine ⟨70268789337066159375059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46845859558044106250039 70268789337066159375059)
        ·
          refine ⟨105403184005599239062589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70268789337066159375059 105403184005599239062589)
          ·
            refine ⟨39526194002099714648471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105403184005599239062589 39526194002099714648471)
            ·
              refine ⟨59289291003149571972707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39526194002099714648471 59289291003149571972707)
              ·
                refine ⟨88933936504724357959061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59289291003149571972707 88933936504724357959061)
                ·
                  refine ⟨4168778273658954279331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88933936504724357959061 4168778273658954279331)
                  ·
                    rfl

theorem cell22_36534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_36534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36534 prefixEnd_36534 := by exact prefixLift 36534
  have htrace : WordTrace (prefixWord ++ tailWord_36534) baseStart_36534 baseEnd_36534 := by
    simpa [prefixWord, tailWord_36534, baseEnd_36534] using wordTrace_append hprefix tailTrace_36534
  have hstable : (prefixWord ++ tailWord_36534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36534).length < 2 ^ (prefixWord ++ tailWord_36534).sum := by decide
  have hdescent : baseEnd_36534 < baseStart_36534 := by decide
  rcases family_descends (prefixWord ++ tailWord_36534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36594 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_36594 : Nat := 118140960795 + 36594 * 2 ^ 59
def prefixEnd_36594 : Nat := 4983230072969 + 3 ^ 40 * 36594 * 2
def baseEnd_36594 : Nat := 12526874047156706337809

theorem tailTrace_36594 : CollatzResearch.WordTrace tailWord_36594 prefixEnd_36594 12526874047156706337809 := by
  unfold tailWord_36594
  simp only [CollatzResearch.WordTrace]
  refine ⟨333673207358415650685209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 889795219622441735160557 333673207358415650685209)
  ·
    refine ⟨250254905518811738013907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 333673207358415650685209 250254905518811738013907)
    ·
      refine ⟨375382358278217607020861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250254905518811738013907 375382358278217607020861)
      ·
        refine ⟨140768384354331602632823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 375382358278217607020861 140768384354331602632823)
        ·
          refine ⟨211152576531497403949235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140768384354331602632823 211152576531497403949235)
          ·
            refine ⟨316728864797246105923853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211152576531497403949235 316728864797246105923853)
            ·
              refine ⟨118773324298967289721445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316728864797246105923853 118773324298967289721445)
              ·
                refine ⟨22269998306056366822771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118773324298967289721445 22269998306056366822771)
                ·
                  refine ⟨33404997459084550234157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22269998306056366822771 33404997459084550234157)
                  ·
                    refine ⟨12526874047156706337809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33404997459084550234157 12526874047156706337809)
                    ·
                      rfl

theorem cell22_36594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_36594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36594 prefixEnd_36594 := by exact prefixLift 36594
  have htrace : WordTrace (prefixWord ++ tailWord_36594) baseStart_36594 baseEnd_36594 := by
    simpa [prefixWord, tailWord_36594, baseEnd_36594] using wordTrace_append hprefix tailTrace_36594
  have hstable : (prefixWord ++ tailWord_36594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36594).length < 2 ^ (prefixWord ++ tailWord_36594).sum := by decide
  have hdescent : baseEnd_36594 < baseStart_36594 := by decide
  rcases family_descends (prefixWord ++ tailWord_36594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36620 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_36620 : Nat := 118140960795 + 36620 * 2 ^ 59
def prefixEnd_36620 : Nat := 4983230072969 + 3 ^ 40 * 36620 * 2
def baseEnd_36620 : Nat := 12535774378501305187729

theorem tailTrace_36620 : CollatzResearch.WordTrace tailWord_36620 prefixEnd_36620 12535774378501305187729 := by
  unfold tailWord_36620
  simp only [CollatzResearch.WordTrace]
  refine ⟨667820563669734521593657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 890427418226312695458209 667820563669734521593657)
  ·
    refine ⟨500865422752300891195243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 667820563669734521593657 500865422752300891195243)
    ·
      refine ⟨751298134128451336792865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500865422752300891195243 751298134128451336792865)
      ·
        refine ⟨563473600596338502594649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751298134128451336792865 563473600596338502594649)
        ·
          refine ⟨422605200447253876945987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563473600596338502594649 422605200447253876945987)
          ·
            refine ⟨633907800670880815418981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422605200447253876945987 633907800670880815418981)
            ·
              refine ⟨118857712625790152891059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 633907800670880815418981 118857712625790152891059)
              ·
                refine ⟨178286568938685229336589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118857712625790152891059 178286568938685229336589)
                ·
                  refine ⟨66857463352006961001221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178286568938685229336589 66857463352006961001221)
                  ·
                    refine ⟨12535774378501305187729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66857463352006961001221 12535774378501305187729)
                    ·
                      rfl

theorem cell22_36620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_36620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36620 prefixEnd_36620 := by exact prefixLift 36620
  have htrace : WordTrace (prefixWord ++ tailWord_36620) baseStart_36620 baseEnd_36620 := by
    simpa [prefixWord, tailWord_36620, baseEnd_36620] using wordTrace_append hprefix tailTrace_36620
  have hstable : (prefixWord ++ tailWord_36620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36620).length < 2 ^ (prefixWord ++ tailWord_36620).sum := by decide
  have hdescent : baseEnd_36620 < baseStart_36620 := by decide
  rcases family_descends (prefixWord ++ tailWord_36620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36633 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_36633 : Nat := 118140960795 + 36633 * 2 ^ 59
def prefixEnd_36633 : Nat := 4983230072969 + 3 ^ 40 * 36633 * 2
def baseEnd_36633 : Nat := 12540224544173604612689

theorem tailTrace_36633 : CollatzResearch.WordTrace tailWord_36633 prefixEnd_36633 12540224544173604612689 := by
  unfold tailWord_36633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336115276292372263410553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 890743517528248175607035 1336115276292372263410553)
  ·
    refine ⟨1002086457219279197557915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1336115276292372263410553 1002086457219279197557915)
    ·
      refine ⟨1503129685828918796336873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002086457219279197557915 1503129685828918796336873)
      ·
        refine ⟨1127347264371689097252655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1503129685828918796336873 1127347264371689097252655)
        ·
          refine ⟨1691020896557533645878983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127347264371689097252655 1691020896557533645878983)
          ·
            refine ⟨2536531344836300468818475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691020896557533645878983 2536531344836300468818475)
            ·
              refine ⟨3804797017254450703227713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536531344836300468818475 3804797017254450703227713)
              ·
                refine ⟨2853597762940838027420785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3804797017254450703227713 2853597762940838027420785)
                ·
                  refine ⟨2140198322205628520565589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853597762940838027420785 2140198322205628520565589)
                  ·
                    refine ⟨12540224544173604612689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2140198322205628520565589 12540224544173604612689)
                    ·
                      rfl

theorem cell22_36633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_36633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36633 prefixEnd_36633 := by exact prefixLift 36633
  have htrace : WordTrace (prefixWord ++ tailWord_36633) baseStart_36633 baseEnd_36633 := by
    simpa [prefixWord, tailWord_36633, baseEnd_36633] using wordTrace_append hprefix tailTrace_36633
  have hstable : (prefixWord ++ tailWord_36633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36633).length < 2 ^ (prefixWord ++ tailWord_36633).sum := by decide
  have hdescent : baseEnd_36633 < baseStart_36633 := by decide
  rcases family_descends (prefixWord ++ tailWord_36633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36652 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_36652 : Nat := 118140960795 + 36652 * 2 ^ 59
def prefixEnd_36652 : Nat := 4983230072969 + 3 ^ 40 * 36652 * 2
def baseEnd_36652 : Nat := 4182242877487962795877

theorem tailTrace_36652 : CollatzResearch.WordTrace tailWord_36652 prefixEnd_36652 4182242877487962795877 := by
  unfold tailWord_36652
  simp only [CollatzResearch.WordTrace]
  refine ⟨668404131611769254176105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 891205508815692338901473 668404131611769254176105)
  ·
    refine ⟨501303098708826940632079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668404131611769254176105 501303098708826940632079)
    ·
      refine ⟨751954648063240410948119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501303098708826940632079 751954648063240410948119)
      ·
        refine ⟨1127931972094860616422179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751954648063240410948119 1127931972094860616422179)
        ·
          refine ⟨1691897958142290924633269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127931972094860616422179 1691897958142290924633269)
          ·
            refine ⟨158615433575839774184369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1691897958142290924633269 158615433575839774184369)
            ·
              refine ⟨118961575181879830638277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158615433575839774184369 118961575181879830638277)
              ·
                refine ⟨22305295346602468244677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118961575181879830638277 22305295346602468244677)
                ·
                  refine ⟨4182242877487962795877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22305295346602468244677 4182242877487962795877)
                  ·
                    rfl

theorem cell22_36652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_36652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36652 prefixEnd_36652 := by exact prefixLift 36652
  have htrace : WordTrace (prefixWord ++ tailWord_36652) baseStart_36652 baseEnd_36652 := by
    simpa [prefixWord, tailWord_36652, baseEnd_36652] using wordTrace_append hprefix tailTrace_36652
  have hstable : (prefixWord ++ tailWord_36652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36652).length < 2 ^ (prefixWord ++ tailWord_36652).sum := by decide
  have hdescent : baseEnd_36652 < baseStart_36652 := by decide
  rcases family_descends (prefixWord ++ tailWord_36652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36680 : List Nat := [2, 1, 3, 1, 1, 5, 1, 8]
def baseStart_36680 : Nat := 118140960795 + 36680 * 2 ^ 59
def prefixEnd_36680 : Nat := 4983230072969 + 3 ^ 40 * 36680 * 2
def baseEnd_36680 : Nat := 1395145956075683187505

theorem tailTrace_36680 : CollatzResearch.WordTrace tailWord_36680 prefixEnd_36680 1395145956075683187505 := by
  unfold tailWord_36680
  simp only [CollatzResearch.WordTrace]
  refine ⟨668914753561049645185747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 891886338081399526914329 668914753561049645185747)
  ·
    refine ⟨1003372130341574467778621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668914753561049645185747 1003372130341574467778621)
    ·
      refine ⟨376264548878090425416983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1003372130341574467778621 376264548878090425416983)
      ·
        refine ⟨564396823317135638125475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376264548878090425416983 564396823317135638125475)
        ·
          refine ⟨846595234975703457188213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564396823317135638125475 846595234975703457188213)
          ·
            refine ⟨79368303278972199111395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 846595234975703457188213 79368303278972199111395)
            ·
              refine ⟨119052454918458298667093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79368303278972199111395 119052454918458298667093)
              ·
                refine ⟨1395145956075683187505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 119052454918458298667093 1395145956075683187505)
                ·
                  rfl

theorem cell22_36680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_36680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36680 prefixEnd_36680 := by exact prefixLift 36680
  have htrace : WordTrace (prefixWord ++ tailWord_36680) baseStart_36680 baseEnd_36680 := by
    simpa [prefixWord, tailWord_36680, baseEnd_36680] using wordTrace_append hprefix tailTrace_36680
  have hstable : (prefixWord ++ tailWord_36680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36680).length < 2 ^ (prefixWord ++ tailWord_36680).sum := by decide
  have hdescent : baseEnd_36680 < baseStart_36680 := by decide
  rcases family_descends (prefixWord ++ tailWord_36680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36714 : List Nat := [3, 1, 3, 4, 1, 1, 2, 7]
def baseStart_36714 : Nat := 118140960795 + 36714 * 2 ^ 59
def prefixEnd_36714 : Nat := 4983230072969 + 3 ^ 40 * 36714 * 2
def baseEnd_36714 : Nat := 1396439166612932593049

theorem tailTrace_36714 : CollatzResearch.WordTrace tailWord_36714 prefixEnd_36714 1396439166612932593049 := by
  unfold tailWord_36714
  simp only [CollatzResearch.WordTrace]
  refine ⟨334767397249730774277299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 892713059332615398072797 334767397249730774277299)
  ·
    refine ⟨502151095874596161415949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334767397249730774277299 502151095874596161415949)
    ·
      refine ⟨188306660952973560530981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 502151095874596161415949 188306660952973560530981)
      ·
        refine ⟨35307498928682542599559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188306660952973560530981 35307498928682542599559)
        ·
          refine ⟨52961248393023813899339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35307498928682542599559 52961248393023813899339)
          ·
            refine ⟨79441872589535720849009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52961248393023813899339 79441872589535720849009)
            ·
              refine ⟨59581404442151790636757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79441872589535720849009 59581404442151790636757)
              ·
                refine ⟨1396439166612932593049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59581404442151790636757 1396439166612932593049)
                ·
                  rfl

theorem cell22_36714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_36714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36714 prefixEnd_36714 := by exact prefixLift 36714
  have htrace : WordTrace (prefixWord ++ tailWord_36714) baseStart_36714 baseEnd_36714 := by
    simpa [prefixWord, tailWord_36714, baseEnd_36714] using wordTrace_append hprefix tailTrace_36714
  have hstable : (prefixWord ++ tailWord_36714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36714).length < 2 ^ (prefixWord ++ tailWord_36714).sum := by decide
  have hdescent : baseEnd_36714 < baseStart_36714 := by decide
  rcases family_descends (prefixWord ++ tailWord_36714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36718 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_36718 : Nat := 118140960795 + 36718 * 2 ^ 59
def prefixEnd_36718 : Nat := 4983230072969 + 3 ^ 40 * 36718 * 2
def baseEnd_36718 : Nat := 12569321781261716237429

theorem tailTrace_36718 : CollatzResearch.WordTrace tailWord_36718 prefixEnd_36718 12569321781261716237429 := by
  unfold tailWord_36718
  simp only [CollatzResearch.WordTrace]
  refine ⟨167401935123053972531851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 892810320656287853503205 167401935123053972531851)
  ·
    refine ⟨251102902684580958797777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167401935123053972531851 251102902684580958797777)
    ·
      refine ⟨188327177013435719098333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251102902684580958797777 188327177013435719098333)
      ·
        refine ⟨70622691380038394661875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188327177013435719098333 70622691380038394661875)
        ·
          refine ⟨105934037070057591992813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70622691380038394661875 105934037070057591992813)
          ·
            refine ⟨39725263901271596997305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105934037070057591992813 39725263901271596997305)
            ·
              refine ⟨29793947925953697747979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39725263901271596997305 29793947925953697747979)
              ·
                refine ⟨44690921888930546621969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29793947925953697747979 44690921888930546621969)
                ·
                  refine ⟨33518191416697909966477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44690921888930546621969 33518191416697909966477)
                  ·
                    refine ⟨12569321781261716237429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33518191416697909966477 12569321781261716237429)
                    ·
                      rfl

theorem cell22_36718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_36718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36718 prefixEnd_36718 := by exact prefixLift 36718
  have htrace : WordTrace (prefixWord ++ tailWord_36718) baseStart_36718 baseEnd_36718 := by
    simpa [prefixWord, tailWord_36718, baseEnd_36718] using wordTrace_append hprefix tailTrace_36718
  have hstable : (prefixWord ++ tailWord_36718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36718).length < 2 ^ (prefixWord ++ tailWord_36718).sum := by decide
  have hdescent : baseEnd_36718 < baseStart_36718 := by decide
  rcases family_descends (prefixWord ++ tailWord_36718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36772 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_36772 : Nat := 118140960795 + 36772 * 2 ^ 59
def prefixEnd_36772 : Nat := 4983230072969 + 3 ^ 40 * 36772 * 2
def baseEnd_36772 : Nat := 12587807084823575387263

theorem tailTrace_36772 : CollatzResearch.WordTrace tailWord_36772 prefixEnd_36772 12587807084823575387263 := by
  unfold tailWord_36772
  simp only [CollatzResearch.WordTrace]
  refine ⟨670592511394399501360285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 894123348525866001813713 670592511394399501360285)
  ·
    refine ⟨251472191772899813010107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 670592511394399501360285 251472191772899813010107)
    ·
      refine ⟨377208287659349719515161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251472191772899813010107 377208287659349719515161)
      ·
        refine ⟨282906215744512289636371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377208287659349719515161 282906215744512289636371)
        ·
          refine ⟨424359323616768434454557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282906215744512289636371 424359323616768434454557)
          ·
            refine ⟨159134746356288162920459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424359323616768434454557 159134746356288162920459)
            ·
              refine ⟨238702119534432244380689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159134746356288162920459 238702119534432244380689)
              ·
                refine ⟨179026589650824183285517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238702119534432244380689 179026589650824183285517)
                ·
                  refine ⟨67134971119059068732069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179026589650824183285517 67134971119059068732069)
                  ·
                    refine ⟨12587807084823575387263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67134971119059068732069 12587807084823575387263)
                    ·
                      rfl

theorem cell22_36772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_36772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36772 prefixEnd_36772 := by exact prefixLift 36772
  have htrace : WordTrace (prefixWord ++ tailWord_36772) baseStart_36772 baseEnd_36772 := by
    simpa [prefixWord, tailWord_36772, baseEnd_36772] using wordTrace_append hprefix tailTrace_36772
  have hstable : (prefixWord ++ tailWord_36772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36772).length < 2 ^ (prefixWord ++ tailWord_36772).sum := by decide
  have hdescent : baseEnd_36772 < baseStart_36772 := by decide
  rcases family_descends (prefixWord ++ tailWord_36772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36815 : List Nat := [1, 1, 2, 1, 1, 5, 11]
def baseStart_36815 : Nat := 118140960795 + 36815 * 2 ^ 59
def prefixEnd_36815 : Nat := 4983230072969 + 3 ^ 40 * 36815 * 2
def baseEnd_36815 : Nat := 466760254206881354153

theorem tailTrace_36815 : CollatzResearch.WordTrace tailWord_36815 prefixEnd_36815 466760254206881354153 := by
  unfold tailWord_36815
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342753361633017346535899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 895168907755344897690599 1342753361633017346535899)
  ·
    refine ⟨2014130042449526019803849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342753361633017346535899 2014130042449526019803849)
    ·
      refine ⟨1510597531837144514852887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2014130042449526019803849 1510597531837144514852887)
      ·
        refine ⟨2265896297755716772279331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510597531837144514852887 2265896297755716772279331)
        ·
          refine ⟨3398844446633575158418997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265896297755716772279331 3398844446633575158418997)
          ·
            refine ⟨318641666871897671101781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3398844446633575158418997 318641666871897671101781)
            ·
              refine ⟨466760254206881354153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 318641666871897671101781 466760254206881354153)
              ·
                rfl

theorem cell22_36815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 11].length) (baseStart_36815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36815 prefixEnd_36815 := by exact prefixLift 36815
  have htrace : WordTrace (prefixWord ++ tailWord_36815) baseStart_36815 baseEnd_36815 := by
    simpa [prefixWord, tailWord_36815, baseEnd_36815] using wordTrace_append hprefix tailTrace_36815
  have hstable : (prefixWord ++ tailWord_36815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36815).length < 2 ^ (prefixWord ++ tailWord_36815).sum := by decide
  have hdescent : baseEnd_36815 < baseStart_36815 := by decide
  rcases family_descends (prefixWord ++ tailWord_36815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36836 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_36836 : Nat := 118140960795 + 36836 * 2 ^ 59
def prefixEnd_36836 : Nat := 4983230072969 + 3 ^ 40 * 36836 * 2
def baseEnd_36836 : Nat := 12609715592748741787067

theorem tailTrace_36836 : CollatzResearch.WordTrace tailWord_36836 prefixEnd_36836 12609715592748741787067 := by
  unfold tailWord_36836
  simp only [CollatzResearch.WordTrace]
  refine ⟨671759647278468966525181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 895679529704625288700241 671759647278468966525181)
  ·
    refine ⟨251909867729425862446943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 671759647278468966525181 251909867729425862446943)
    ·
      refine ⟨377864801594138793670415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251909867729425862446943 377864801594138793670415)
      ·
        refine ⟨566797202391208190505623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377864801594138793670415 566797202391208190505623)
        ·
          refine ⟨850195803586812285758435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566797202391208190505623 850195803586812285758435)
          ·
            refine ⟨1275293705380218428637653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850195803586812285758435 1275293705380218428637653)
            ·
              refine ⟨29889696219848869421195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1275293705380218428637653 29889696219848869421195)
              ·
                refine ⟨44834544329773304131793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29889696219848869421195 44834544329773304131793)
                ·
                  refine ⟨33625908247329978098845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44834544329773304131793 33625908247329978098845)
                  ·
                    refine ⟨12609715592748741787067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33625908247329978098845 12609715592748741787067)
                    ·
                      rfl

theorem cell22_36836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_36836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36836 prefixEnd_36836 := by exact prefixLift 36836
  have htrace : WordTrace (prefixWord ++ tailWord_36836) baseStart_36836 baseEnd_36836 := by
    simpa [prefixWord, tailWord_36836, baseEnd_36836] using wordTrace_append hprefix tailTrace_36836
  have hstable : (prefixWord ++ tailWord_36836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36836).length < 2 ^ (prefixWord ++ tailWord_36836).sum := by decide
  have hdescent : baseEnd_36836 < baseStart_36836 := by decide
  rcases family_descends (prefixWord ++ tailWord_36836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36937 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_36937 : Nat := 118140960795 + 36937 * 2 ^ 59
def prefixEnd_36937 : Nat := 4983230072969 + 3 ^ 40 * 36937 * 2
def baseEnd_36937 : Nat := 12644289956818145011757

theorem tailTrace_36937 : CollatzResearch.WordTrace tailWord_36937 prefixEnd_36937 12644289956818145011757 := by
  unfold tailWord_36937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347203067191032182477065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 898135378127354788318043 1347203067191032182477065)
  ·
    refine ⟨1010402300393274136857799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1347203067191032182477065 1010402300393274136857799)
    ·
      refine ⟨1515603450589911205286699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010402300393274136857799 1515603450589911205286699)
      ·
        refine ⟨2273405175884866807930049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515603450589911205286699 2273405175884866807930049)
        ·
          refine ⟨1705053881913650105947537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273405175884866807930049 1705053881913650105947537)
          ·
            refine ⟨1278790411435237579460653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705053881913650105947537 1278790411435237579460653)
            ·
              refine ⟨479546404288214092297745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278790411435237579460653 479546404288214092297745)
              ·
                refine ⟨359659803216160569223309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479546404288214092297745 359659803216160569223309)
                ·
                  refine ⟨134872426206060213458741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359659803216160569223309 134872426206060213458741)
                  ·
                    refine ⟨12644289956818145011757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134872426206060213458741 12644289956818145011757)
                    ·
                      rfl

theorem cell22_36937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_36937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36937 prefixEnd_36937 := by exact prefixLift 36937
  have htrace : WordTrace (prefixWord ++ tailWord_36937) baseStart_36937 baseEnd_36937 := by
    simpa [prefixWord, tailWord_36937, baseEnd_36937] using wordTrace_append hprefix tailTrace_36937
  have hstable : (prefixWord ++ tailWord_36937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36937).length < 2 ^ (prefixWord ++ tailWord_36937).sum := by decide
  have hdescent : baseEnd_36937 < baseStart_36937 := by decide
  rcases family_descends (prefixWord ++ tailWord_36937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36939 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 4]
def baseStart_36939 : Nat := 118140960795 + 36939 * 2 ^ 59
def prefixEnd_36939 : Nat := 4983230072969 + 3 ^ 40 * 36939 * 2
def baseEnd_36939 : Nat := 4214991532563602153917

theorem tailTrace_36939 : CollatzResearch.WordTrace tailWord_36939 prefixEnd_36939 4214991532563602153917 := by
  unfold tailWord_36939
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347276013183786524049871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 898184008789191016033247 1347276013183786524049871)
  ·
    refine ⟨2020914019775679786074807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1347276013183786524049871 2020914019775679786074807)
    ·
      refine ⟨3031371029663519679112211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020914019775679786074807 3031371029663519679112211)
      ·
        refine ⟨4547056544495279518668317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031371029663519679112211 4547056544495279518668317)
        ·
          refine ⟨1705146204185729819500619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4547056544495279518668317 1705146204185729819500619)
          ·
            refine ⟨2557719306278594729250929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705146204185729819500619 2557719306278594729250929)
            ·
              refine ⟨1918289479708946046938197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2557719306278594729250929 1918289479708946046938197)
              ·
                refine ⟨22479954840339211487557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1918289479708946046938197 22479954840339211487557)
                ·
                  refine ⟨4214991532563602153917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22479954840339211487557 4214991532563602153917)
                  ·
                    rfl

theorem cell22_36939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 4].length) (baseStart_36939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36939 prefixEnd_36939 := by exact prefixLift 36939
  have htrace : WordTrace (prefixWord ++ tailWord_36939) baseStart_36939 baseEnd_36939 := by
    simpa [prefixWord, tailWord_36939, baseEnd_36939] using wordTrace_append hprefix tailTrace_36939
  have hstable : (prefixWord ++ tailWord_36939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36939).length < 2 ^ (prefixWord ++ tailWord_36939).sum := by decide
  have hdescent : baseEnd_36939 < baseStart_36939 := by decide
  rcases family_descends (prefixWord ++ tailWord_36939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36954 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_36954 : Nat := 118140960795 + 36954 * 2 ^ 59
def prefixEnd_36954 : Nat := 4983230072969 + 3 ^ 40 * 36954 * 2
def baseEnd_36954 : Nat := 12650109404235767336705

theorem tailTrace_36954 : CollatzResearch.WordTrace tailWord_36954 prefixEnd_36954 12650109404235767336705 := by
  unfold tailWord_36954
  simp only [CollatzResearch.WordTrace]
  refine ⟨336955777032361021461479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 898548738752962723897277 336955777032361021461479)
  ·
    refine ⟨505433665548541532192219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 336955777032361021461479 505433665548541532192219)
    ·
      refine ⟨758150498322812298288329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505433665548541532192219 758150498322812298288329)
      ·
        refine ⟨568612873742109223716247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758150498322812298288329 568612873742109223716247)
        ·
          refine ⟨852919310613163835574371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568612873742109223716247 852919310613163835574371)
          ·
            refine ⟨1279378965919745753361557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852919310613163835574371 1279378965919745753361557)
            ·
              refine ⟨59970889027488082188823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1279378965919745753361557 59970889027488082188823)
              ·
                refine ⟨89956333541232123283235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59970889027488082188823 89956333541232123283235)
                ·
                  refine ⟨134934500311848184924853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89956333541232123283235 134934500311848184924853)
                  ·
                    refine ⟨12650109404235767336705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134934500311848184924853 12650109404235767336705)
                    ·
                      rfl

theorem cell22_36954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_36954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36954 prefixEnd_36954 := by exact prefixLift 36954
  have htrace : WordTrace (prefixWord ++ tailWord_36954) baseStart_36954 baseEnd_36954 := by
    simpa [prefixWord, tailWord_36954, baseEnd_36954] using wordTrace_append hprefix tailTrace_36954
  have hstable : (prefixWord ++ tailWord_36954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36954).length < 2 ^ (prefixWord ++ tailWord_36954).sum := by decide
  have hdescent : baseEnd_36954 < baseStart_36954 := by decide
  rcases family_descends (prefixWord ++ tailWord_36954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36988 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_36988 : Nat := 118140960795 + 36988 * 2 ^ 59
def prefixEnd_36988 : Nat := 4983230072969 + 3 ^ 40 * 36988 * 2
def baseEnd_36988 : Nat := 12661748299071011986601

theorem tailTrace_36988 : CollatzResearch.WordTrace tailWord_36988 prefixEnd_36988 12661748299071011986601 := by
  unfold tailWord_36988
  simp only [CollatzResearch.WordTrace]
  refine ⟨674531595003133946291809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 899375460004178595055745 674531595003133946291809)
  ·
    refine ⟨505898696252350459718857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 674531595003133946291809 505898696252350459718857)
    ·
      refine ⟨379424022189262844789143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 505898696252350459718857 379424022189262844789143)
      ·
        refine ⟨569136033283894267183715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379424022189262844789143 569136033283894267183715)
        ·
          refine ⟨853704049925841400775573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569136033283894267183715 853704049925841400775573)
          ·
            refine ⟨40017377340273815661355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 853704049925841400775573 40017377340273815661355)
            ·
              refine ⟨60026066010410723492033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40017377340273815661355 60026066010410723492033)
              ·
                refine ⟨45019549507808042619025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60026066010410723492033 45019549507808042619025)
                ·
                  refine ⟨33764662130856031964269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45019549507808042619025 33764662130856031964269)
                  ·
                    refine ⟨12661748299071011986601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33764662130856031964269 12661748299071011986601)
                    ·
                      rfl

theorem cell22_36988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_36988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_36988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_36988 prefixEnd_36988 := by exact prefixLift 36988
  have htrace : WordTrace (prefixWord ++ tailWord_36988) baseStart_36988 baseEnd_36988 := by
    simpa [prefixWord, tailWord_36988, baseEnd_36988] using wordTrace_append hprefix tailTrace_36988
  have hstable : (prefixWord ++ tailWord_36988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36988).length < 2 ^ (prefixWord ++ tailWord_36988).sum := by decide
  have hdescent : baseEnd_36988 < baseStart_36988 := by decide
  rcases family_descends (prefixWord ++ tailWord_36988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37018 : List Nat := [3, 1, 1, 5, 2, 2, 2, 6]
def baseStart_37018 : Nat := 118140960795 + 37018 * 2 ^ 59
def prefixEnd_37018 : Nat := 4983230072969 + 3 ^ 40 * 37018 * 2
def baseEnd_37018 : Nat := 1408001990240103748501

theorem tailTrace_37018 : CollatzResearch.WordTrace tailWord_37018 prefixEnd_37018 1408001990240103748501 := by
  unfold tailWord_37018
  simp only [CollatzResearch.WordTrace]
  refine ⟨337539344974395754043927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 900104919931722010783805 337539344974395754043927)
  ·
    refine ⟨506309017461593631065891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 337539344974395754043927 506309017461593631065891)
    ·
      refine ⟨759463526192390446598837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506309017461593631065891 759463526192390446598837)
      ·
        refine ⟨71199705580536604368641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 759463526192390446598837 71199705580536604368641)
        ·
          refine ⟨53399779185402453276481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71199705580536604368641 53399779185402453276481)
          ·
            refine ⟨40049834389051839957361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53399779185402453276481 40049834389051839957361)
            ·
              refine ⟨30037375791788879968021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40049834389051839957361 30037375791788879968021)
              ·
                refine ⟨1408001990240103748501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30037375791788879968021 1408001990240103748501)
                ·
                  rfl

theorem cell22_37018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_37018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37018 prefixEnd_37018 := by exact prefixLift 37018
  have htrace : WordTrace (prefixWord ++ tailWord_37018) baseStart_37018 baseEnd_37018 := by
    simpa [prefixWord, tailWord_37018, baseEnd_37018] using wordTrace_append hprefix tailTrace_37018
  have hstable : (prefixWord ++ tailWord_37018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37018).length < 2 ^ (prefixWord ++ tailWord_37018).sum := by decide
  have hdescent : baseEnd_37018 < baseStart_37018 := by decide
  rcases family_descends (prefixWord ++ tailWord_37018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37157 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_37157 : Nat := 118140960795 + 37157 * 2 ^ 59
def prefixEnd_37157 : Nat := 4983230072969 + 3 ^ 40 * 37157 * 2
def baseEnd_37157 : Nat := 12719600452810904511083

theorem tailTrace_37157 : CollatzResearch.WordTrace tailWord_37157 prefixEnd_37157 12719600452810904511083 := by
  unfold tailWord_37157
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355227126394009755485725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 903484750929339836990483 1355227126394009755485725)
  ·
    refine ⟨508210172397753658307147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1355227126394009755485725 508210172397753658307147)
    ·
      refine ⟨762315258596630487460721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508210172397753658307147 762315258596630487460721)
      ·
        refine ⟨571736443947472865595541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 762315258596630487460721 571736443947472865595541)
        ·
          refine ⟨26800145810037790574791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 571736443947472865595541 26800145810037790574791)
          ·
            refine ⟨40200218715056685862187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26800145810037790574791 40200218715056685862187)
            ·
              refine ⟨60300328072585028793281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40200218715056685862187 60300328072585028793281)
              ·
                refine ⟨45225246054438771594961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60300328072585028793281 45225246054438771594961)
                ·
                  refine ⟨33918934540829078696221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45225246054438771594961 33918934540829078696221)
                  ·
                    refine ⟨12719600452810904511083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33918934540829078696221 12719600452810904511083)
                    ·
                      rfl

theorem cell22_37157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_37157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37157 prefixEnd_37157 := by exact prefixLift 37157
  have htrace : WordTrace (prefixWord ++ tailWord_37157) baseStart_37157 baseEnd_37157 := by
    simpa [prefixWord, tailWord_37157, baseEnd_37157] using wordTrace_append hprefix tailTrace_37157
  have hstable : (prefixWord ++ tailWord_37157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37157).length < 2 ^ (prefixWord ++ tailWord_37157).sum := by decide
  have hdescent : baseEnd_37157 < baseStart_37157 := by decide
  rcases family_descends (prefixWord ++ tailWord_37157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37241 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_37241 : Nat := 118140960795 + 37241 * 2 ^ 59
def prefixEnd_37241 : Nat := 4983230072969 + 3 ^ 40 * 37241 * 2
def baseEnd_37241 : Nat := 12748355369462685410825

theorem tailTrace_37241 : CollatzResearch.WordTrace tailWord_37241 prefixEnd_37241 12748355369462685410825 := by
  unfold tailWord_37241
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358290858089692101543577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 905527238726461401029051 1358290858089692101543577)
  ·
    refine ⟨1018718143567269076157683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1358290858089692101543577 1018718143567269076157683)
    ·
      refine ⟨1528077215350903614236525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018718143567269076157683 1528077215350903614236525)
      ·
        refine ⟨573028955756588855338697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1528077215350903614236525 573028955756588855338697)
        ·
          refine ⟨429771716817441641504023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573028955756588855338697 429771716817441641504023)
          ·
            refine ⟨644657575226162462256035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429771716817441641504023 644657575226162462256035)
            ·
              refine ⟨966986362839243693384053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644657575226162462256035 966986362839243693384053)
              ·
                refine ⟨90654971516179096254755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966986362839243693384053 90654971516179096254755)
                ·
                  refine ⟨135982457274268644382133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90654971516179096254755 135982457274268644382133)
                  ·
                    refine ⟨12748355369462685410825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135982457274268644382133 12748355369462685410825)
                    ·
                      rfl

theorem cell22_37241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_37241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37241 prefixEnd_37241 := by exact prefixLift 37241
  have htrace : WordTrace (prefixWord ++ tailWord_37241) baseStart_37241 baseEnd_37241 := by
    simpa [prefixWord, tailWord_37241, baseEnd_37241] using wordTrace_append hprefix tailTrace_37241
  have hstable : (prefixWord ++ tailWord_37241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37241).length < 2 ^ (prefixWord ++ tailWord_37241).sum := by decide
  have hdescent : baseEnd_37241 < baseStart_37241 := by decide
  rcases family_descends (prefixWord ++ tailWord_37241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37245 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_37245 : Nat := 118140960795 + 37245 * 2 ^ 59
def prefixEnd_37245 : Nat := 4983230072969 + 3 ^ 40 * 37245 * 2
def baseEnd_37245 : Nat := 12749724651208008310813

theorem tailTrace_37245 : CollatzResearch.WordTrace tailWord_37245 prefixEnd_37245 12749724651208008310813 := by
  unfold tailWord_37245
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358436750075200784689189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 905624500050133856459459 1358436750075200784689189)
  ·
    refine ⟨254706890639100147129223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1358436750075200784689189 254706890639100147129223)
    ·
      refine ⟨382060335958650220693835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254706890639100147129223 382060335958650220693835)
      ·
        refine ⟨573090503937975331040753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382060335958650220693835 573090503937975331040753)
        ·
          refine ⟨429817877953481498280565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573090503937975331040753 429817877953481498280565)
          ·
            refine ⟨40295426058138890463803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 429817877953481498280565 40295426058138890463803)
            ·
              refine ⟨60443139087208335695705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40295426058138890463803 60443139087208335695705)
              ·
                refine ⟨45332354315406251771779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60443139087208335695705 45332354315406251771779)
                ·
                  refine ⟨67998531473109377657669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45332354315406251771779 67998531473109377657669)
                  ·
                    refine ⟨12749724651208008310813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67998531473109377657669 12749724651208008310813)
                    ·
                      rfl

theorem cell22_37245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_37245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37245 prefixEnd_37245 := by exact prefixLift 37245
  have htrace : WordTrace (prefixWord ++ tailWord_37245) baseStart_37245 baseEnd_37245 := by
    simpa [prefixWord, tailWord_37245, baseEnd_37245] using wordTrace_append hprefix tailTrace_37245
  have hstable : (prefixWord ++ tailWord_37245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37245).length < 2 ^ (prefixWord ++ tailWord_37245).sum := by decide
  have hdescent : baseEnd_37245 < baseStart_37245 := by decide
  rcases family_descends (prefixWord ++ tailWord_37245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37262 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_37262 : Nat := 118140960795 + 37262 * 2 ^ 59
def prefixEnd_37262 : Nat := 4983230072969 + 3 ^ 40 * 37262 * 2
def baseEnd_37262 : Nat := 12755544098625630635761

theorem tailTrace_37262 : CollatzResearch.WordTrace tailWord_37262 prefixEnd_37262 12755544098625630635761 := by
  unfold tailWord_37262
  simp only [CollatzResearch.WordTrace]
  refine ⟨169882098876701586007255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 906037860675741792038693 169882098876701586007255)
  ·
    refine ⟨254823148315052379010883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169882098876701586007255 254823148315052379010883)
    ·
      refine ⟨382234722472578568516325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254823148315052379010883 382234722472578568516325)
      ·
        refine ⟨71669010463608481596811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 382234722472578568516325 71669010463608481596811)
        ·
          refine ⟨107503515695412722395217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71669010463608481596811 107503515695412722395217)
          ·
            refine ⟨80627636771559541796413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107503515695412722395217 80627636771559541796413)
            ·
              refine ⟨30235363789334828173655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80627636771559541796413 30235363789334828173655)
              ·
                refine ⟨45353045684002242260483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30235363789334828173655 45353045684002242260483)
                ·
                  refine ⟨68029568526003363390725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45353045684002242260483 68029568526003363390725)
                  ·
                    refine ⟨12755544098625630635761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68029568526003363390725 12755544098625630635761)
                    ·
                      rfl

theorem cell22_37262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_37262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37262 prefixEnd_37262 := by exact prefixLift 37262
  have htrace : WordTrace (prefixWord ++ tailWord_37262) baseStart_37262 baseEnd_37262 := by
    simpa [prefixWord, tailWord_37262, baseEnd_37262] using wordTrace_append hprefix tailTrace_37262
  have hstable : (prefixWord ++ tailWord_37262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37262).length < 2 ^ (prefixWord ++ tailWord_37262).sum := by decide
  have hdescent : baseEnd_37262 < baseStart_37262 := by decide
  rcases family_descends (prefixWord ++ tailWord_37262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37270 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_37270 : Nat := 118140960795 + 37270 * 2 ^ 59
def prefixEnd_37270 : Nat := 4983230072969 + 3 ^ 40 * 37270 * 2
def baseEnd_37270 : Nat := 12758282662116276435737

theorem tailTrace_37270 : CollatzResearch.WordTrace tailWord_37270 prefixEnd_37270 12758282662116276435737 := by
  unfold tailWord_37270
  simp only [CollatzResearch.WordTrace]
  refine ⟨84959285936539378396829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 906232383323086702899509 84959285936539378396829)
  ·
    refine ⟨31859732226202266898811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84959285936539378396829 31859732226202266898811)
    ·
      refine ⟨47789598339303400348217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31859732226202266898811 47789598339303400348217)
      ·
        refine ⟨35842198754477550261163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47789598339303400348217 35842198754477550261163)
        ·
          refine ⟨53763298131716325391745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35842198754477550261163 53763298131716325391745)
          ·
            refine ⟨40322473598787244043809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53763298131716325391745 40322473598787244043809)
            ·
              refine ⟨30241855199090433032857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40322473598787244043809 30241855199090433032857)
              ·
                refine ⟨22681391399317824774643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30241855199090433032857 22681391399317824774643)
                ·
                  refine ⟨34022087098976737161965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22681391399317824774643 34022087098976737161965)
                  ·
                    refine ⟨12758282662116276435737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34022087098976737161965 12758282662116276435737)
                    ·
                      rfl

theorem cell22_37270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_37270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37270 prefixEnd_37270 := by exact prefixLift 37270
  have htrace : WordTrace (prefixWord ++ tailWord_37270) baseStart_37270 baseEnd_37270 := by
    simpa [prefixWord, tailWord_37270, baseEnd_37270] using wordTrace_append hprefix tailTrace_37270
  have hstable : (prefixWord ++ tailWord_37270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37270).length < 2 ^ (prefixWord ++ tailWord_37270).sum := by decide
  have hdescent : baseEnd_37270 < baseStart_37270 := by decide
  rcases family_descends (prefixWord ++ tailWord_37270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37303 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 5, 3]
def baseStart_37303 : Nat := 118140960795 + 37303 * 2 ^ 59
def prefixEnd_37303 : Nat := 4983230072969 + 3 ^ 40 * 37303 * 2
def baseEnd_37303 : Nat := 12769579236515190360635

theorem tailTrace_37303 : CollatzResearch.WordTrace tailWord_37303 prefixEnd_37303 12769579236515190360635 := by
  unfold tailWord_37303
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360552183865076690300563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 907034789243384460200375 1360552183865076690300563)
  ·
    refine ⟨2040828275797615035450845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360552183865076690300563 2040828275797615035450845)
    ·
      refine ⟨765310603424105638294067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2040828275797615035450845 765310603424105638294067)
      ·
        refine ⟨1147965905136158457441101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765310603424105638294067 1147965905136158457441101)
        ·
          refine ⟨430487214426059421540413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1147965905136158457441101 430487214426059421540413)
          ·
            refine ⟨161432705409772283077655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 430487214426059421540413 161432705409772283077655)
            ·
              refine ⟨242149058114658424616483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161432705409772283077655 242149058114658424616483)
              ·
                refine ⟨363223587171987636924725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242149058114658424616483 363223587171987636924725)
                ·
                  refine ⟨34052211297373840961693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363223587171987636924725 34052211297373840961693)
                  ·
                    refine ⟨12769579236515190360635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34052211297373840961693 12769579236515190360635)
                    ·
                      rfl

theorem cell22_37303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_37303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37303 prefixEnd_37303 := by exact prefixLift 37303
  have htrace : WordTrace (prefixWord ++ tailWord_37303) baseStart_37303 baseEnd_37303 := by
    simpa [prefixWord, tailWord_37303, baseEnd_37303] using wordTrace_append hprefix tailTrace_37303
  have hstable : (prefixWord ++ tailWord_37303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37303).length < 2 ^ (prefixWord ++ tailWord_37303).sum := by decide
  have hdescent : baseEnd_37303 < baseStart_37303 := by decide
  rcases family_descends (prefixWord ++ tailWord_37303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37313 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 1, 4]
def baseStart_37313 : Nat := 118140960795 + 37313 * 2 ^ 59
def prefixEnd_37313 : Nat := 4983230072969 + 3 ^ 40 * 37313 * 2
def baseEnd_37313 : Nat := 12773002440878497610605

theorem tailTrace_37313 : CollatzResearch.WordTrace tailWord_37313 prefixEnd_37313 12773002440878497610605 := by
  unfold tailWord_37313
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360916913828848398164593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 907277942552565598776395 1360916913828848398164593)
  ·
    refine ⟨1020687685371636298623445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1360916913828848398164593 1020687685371636298623445)
    ·
      refine ⟨23922367625897725748987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1020687685371636298623445 23922367625897725748987)
      ·
        refine ⟨35883551438846588623481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23922367625897725748987 35883551438846588623481)
        ·
          refine ⟨26912663579134941467611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35883551438846588623481 26912663579134941467611)
          ·
            refine ⟨40368995368702412201417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26912663579134941467611 40368995368702412201417)
            ·
              refine ⟨30276746526526809151063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40368995368702412201417 30276746526526809151063)
              ·
                refine ⟨45415119789790213726595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30276746526526809151063 45415119789790213726595)
                ·
                  refine ⟨68122679684685320589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45415119789790213726595 68122679684685320589893)
                  ·
                    refine ⟨12773002440878497610605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68122679684685320589893 12773002440878497610605)
                    ·
                      rfl

theorem cell22_37313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_37313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37313 prefixEnd_37313 := by exact prefixLift 37313
  have htrace : WordTrace (prefixWord ++ tailWord_37313) baseStart_37313 baseEnd_37313 := by
    simpa [prefixWord, tailWord_37313, baseEnd_37313] using wordTrace_append hprefix tailTrace_37313
  have hstable : (prefixWord ++ tailWord_37313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37313).length < 2 ^ (prefixWord ++ tailWord_37313).sum := by decide
  have hdescent : baseEnd_37313 < baseStart_37313 := by decide
  rcases family_descends (prefixWord ++ tailWord_37313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37333 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 7]
def baseStart_37333 : Nat := 118140960795 + 37333 * 2 ^ 59
def prefixEnd_37333 : Nat := 4983230072969 + 3 ^ 40 * 37333 * 2
def baseEnd_37333 : Nat := 4259949616535037370181

theorem tailTrace_37333 : CollatzResearch.WordTrace tailWord_37333 prefixEnd_37333 4259949616535037370181 := by
  unfold tailWord_37333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361646373756391813892653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 907764249170927875928435 1361646373756391813892653)
  ·
    refine ⟨510617390158646930209745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1361646373756391813892653 510617390158646930209745)
    ·
      refine ⟨382963042618985197657309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510617390158646930209745 382963042618985197657309)
      ·
        refine ⟨143611140982119449121491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382963042618985197657309 143611140982119449121491)
        ·
          refine ⟨215416711473179173682237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143611140982119449121491 215416711473179173682237)
          ·
            refine ⟨80781266802442190130839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215416711473179173682237 80781266802442190130839)
            ·
              refine ⟨121171900203663285196259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80781266802442190130839 121171900203663285196259)
              ·
                refine ⟨181757850305494927794389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121171900203663285196259 181757850305494927794389)
                ·
                  refine ⟨4259949616535037370181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181757850305494927794389 4259949616535037370181)
                  ·
                    rfl

theorem cell22_37333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_37333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37333 prefixEnd_37333 := by exact prefixLift 37333
  have htrace : WordTrace (prefixWord ++ tailWord_37333) baseStart_37333 baseEnd_37333 := by
    simpa [prefixWord, tailWord_37333, baseEnd_37333] using wordTrace_append hprefix tailTrace_37333
  have hstable : (prefixWord ++ tailWord_37333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37333).length < 2 ^ (prefixWord ++ tailWord_37333).sum := by decide
  have hdescent : baseEnd_37333 < baseStart_37333 := by decide
  rcases family_descends (prefixWord ++ tailWord_37333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37446 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_37446 : Nat := 118140960795 + 37446 * 2 ^ 59
def prefixEnd_37446 : Nat := 4983230072969 + 3 ^ 40 * 37446 * 2
def baseEnd_37446 : Nat := 4272843686303494678399

theorem tailTrace_37446 : CollatzResearch.WordTrace tailWord_37446 prefixEnd_37446 4272843686303494678399 := by
  unfold tailWord_37446
  simp only [CollatzResearch.WordTrace]
  refine ⟨42680244448344128523631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 910511881564674741837461 42680244448344128523631)
  ·
    refine ⟨64020366672516192785447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42680244448344128523631 64020366672516192785447)
    ·
      refine ⟨96030550008774289178171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64020366672516192785447 96030550008774289178171)
      ·
        refine ⟨144045825013161433767257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96030550008774289178171 144045825013161433767257)
        ·
          refine ⟨108034368759871075325443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144045825013161433767257 108034368759871075325443)
          ·
            refine ⟨162051553139806612988165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108034368759871075325443 162051553139806612988165)
            ·
              refine ⟨30384666213713739935281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162051553139806612988165 30384666213713739935281)
              ·
                refine ⟨22788499660285304951461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30384666213713739935281 22788499660285304951461)
                ·
                  refine ⟨4272843686303494678399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22788499660285304951461 4272843686303494678399)
                  ·
                    rfl

theorem cell22_37446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_37446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37446 prefixEnd_37446 := by exact prefixLift 37446
  have htrace : WordTrace (prefixWord ++ tailWord_37446) baseStart_37446 baseEnd_37446 := by
    simpa [prefixWord, tailWord_37446, baseEnd_37446] using wordTrace_append hprefix tailTrace_37446
  have hstable : (prefixWord ++ tailWord_37446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37446).length < 2 ^ (prefixWord ++ tailWord_37446).sum := by decide
  have hdescent : baseEnd_37446 < baseStart_37446 := by decide
  rcases family_descends (prefixWord ++ tailWord_37446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37474 : List Nat := [3, 3, 2, 3, 1, 1, 3, 6]
def baseStart_37474 : Nat := 118140960795 + 37474 * 2 ^ 59
def prefixEnd_37474 : Nat := 4983230072969 + 3 ^ 40 * 37474 * 2
def baseEnd_37474 : Nat := 1425346225680860481679

theorem tailTrace_37474 : CollatzResearch.WordTrace tailWord_37474 prefixEnd_37474 1425346225680860481679 := by
  unfold tailWord_37474
  simp only [CollatzResearch.WordTrace]
  refine ⟨341697266561393223693869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 911192710830381929850317 341697266561393223693869)
  ·
    refine ⟨128136474960522458885201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 341697266561393223693869 128136474960522458885201)
    ·
      refine ⟨96102356220391844163901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128136474960522458885201 96102356220391844163901)
      ·
        refine ⟨36038383582646941561463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96102356220391844163901 36038383582646941561463)
        ·
          refine ⟨54057575373970412342195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36038383582646941561463 54057575373970412342195)
          ·
            refine ⟨81086363060955618513293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54057575373970412342195 81086363060955618513293)
            ·
              refine ⟨30407386147858356942485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81086363060955618513293 30407386147858356942485)
              ·
                refine ⟨1425346225680860481679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30407386147858356942485 1425346225680860481679)
                ·
                  rfl

theorem cell22_37474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_37474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37474 prefixEnd_37474 := by exact prefixLift 37474
  have htrace : WordTrace (prefixWord ++ tailWord_37474) baseStart_37474 baseEnd_37474 := by
    simpa [prefixWord, tailWord_37474, baseEnd_37474] using wordTrace_append hprefix tailTrace_37474
  have hstable : (prefixWord ++ tailWord_37474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37474).length < 2 ^ (prefixWord ++ tailWord_37474).sum := by decide
  have hdescent : baseEnd_37474 < baseStart_37474 := by decide
  rcases family_descends (prefixWord ++ tailWord_37474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37532 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_37532 : Nat := 118140960795 + 37532 * 2 ^ 59
def prefixEnd_37532 : Nat := 4983230072969 + 3 ^ 40 * 37532 * 2
def baseEnd_37532 : Nat := 12847970616434926384933

theorem tailTrace_37532 : CollatzResearch.WordTrace tailWord_37532 prefixEnd_37532 12847970616434926384933 := by
  unfold tailWord_37532
  simp only [CollatzResearch.WordTrace]
  refine ⟨684452250017724400193425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 912603000023632533591233 684452250017724400193425)
  ·
    refine ⟨513339187513293300145069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 684452250017724400193425 513339187513293300145069)
    ·
      refine ⟨192502195317484987554401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 513339187513293300145069 192502195317484987554401)
      ·
        refine ⟨144376646488113740665801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192502195317484987554401 144376646488113740665801)
        ·
          refine ⟨108282484866085305499351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144376646488113740665801 108282484866085305499351)
          ·
            refine ⟨162423727299127958249027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108282484866085305499351 162423727299127958249027)
            ·
              refine ⟨243635590948691937373541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162423727299127958249027 243635590948691937373541)
              ·
                refine ⟨45681673302879738257539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243635590948691937373541 45681673302879738257539)
                ·
                  refine ⟨68522509954319607386309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45681673302879738257539 68522509954319607386309)
                  ·
                    refine ⟨12847970616434926384933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68522509954319607386309 12847970616434926384933)
                    ·
                      rfl

theorem cell22_37532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_37532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37532 prefixEnd_37532 := by exact prefixLift 37532
  have htrace : WordTrace (prefixWord ++ tailWord_37532) baseStart_37532 baseEnd_37532 := by
    simpa [prefixWord, tailWord_37532, baseEnd_37532] using wordTrace_append hprefix tailTrace_37532
  have hstable : (prefixWord ++ tailWord_37532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37532).length < 2 ^ (prefixWord ++ tailWord_37532).sum := by decide
  have hdescent : baseEnd_37532 < baseStart_37532 := by decide
  rcases family_descends (prefixWord ++ tailWord_37532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37545 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_37545 : Nat := 118140960795 + 37545 * 2 ^ 59
def prefixEnd_37545 : Nat := 4983230072969 + 3 ^ 40 * 37545 * 2
def baseEnd_37545 : Nat := 12852420782107225809893

theorem tailTrace_37545 : CollatzResearch.WordTrace tailWord_37545 prefixEnd_37545 12852420782107225809893 := by
  unfold tailWord_37545
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369378648988352020610089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 912919099325568013740059 1369378648988352020610089)
  ·
    refine ⟨1027033986741264015457567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1369378648988352020610089 1027033986741264015457567)
    ·
      refine ⟨1540550980111896023186351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027033986741264015457567 1540550980111896023186351)
      ·
        refine ⟨2310826470167844034779527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540550980111896023186351 2310826470167844034779527)
        ·
          refine ⟨3466239705251766052169291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310826470167844034779527 3466239705251766052169291)
          ·
            refine ⟨5199359557877649078253937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466239705251766052169291 5199359557877649078253937)
            ·
              refine ⟨3899519668408236808690453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5199359557877649078253937 3899519668408236808690453)
              ·
                refine ⟨182789984456636100407365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3899519668408236808690453 182789984456636100407365)
                ·
                  refine ⟨34273122085619268826381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182789984456636100407365 34273122085619268826381)
                  ·
                    refine ⟨12852420782107225809893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34273122085619268826381 12852420782107225809893)
                    ·
                      rfl

theorem cell22_37545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_37545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37545 prefixEnd_37545 := by exact prefixLift 37545
  have htrace : WordTrace (prefixWord ++ tailWord_37545) baseStart_37545 baseEnd_37545 := by
    simpa [prefixWord, tailWord_37545, baseEnd_37545] using wordTrace_append hprefix tailTrace_37545
  have hstable : (prefixWord ++ tailWord_37545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37545).length < 2 ^ (prefixWord ++ tailWord_37545).sum := by decide
  have hdescent : baseEnd_37545 < baseStart_37545 := by decide
  rcases family_descends (prefixWord ++ tailWord_37545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37562 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_37562 : Nat := 118140960795 + 37562 * 2 ^ 59
def prefixEnd_37562 : Nat := 4983230072969 + 3 ^ 40 * 37562 * 2
def baseEnd_37562 : Nat := 12858240229524848134841

theorem tailTrace_37562 : CollatzResearch.WordTrace tailWord_37562 prefixEnd_37562 12858240229524848134841 := by
  unfold tailWord_37562
  simp only [CollatzResearch.WordTrace]
  refine ⟨342499672481690980994735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 913332459951175949319293 342499672481690980994735)
  ·
    refine ⟨513749508722536471492103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342499672481690980994735 513749508722536471492103)
    ·
      refine ⟨770624263083804707238155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513749508722536471492103 770624263083804707238155)
      ·
        refine ⟨1155936394625707060857233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770624263083804707238155 1155936394625707060857233)
        ·
          refine ⟨866952295969280295642925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155936394625707060857233 866952295969280295642925)
          ·
            refine ⟨325107110988480110866097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 866952295969280295642925 325107110988480110866097)
            ·
              refine ⟨243830333241360083149573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325107110988480110866097 243830333241360083149573)
              ·
                refine ⟨45718187482755015590545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243830333241360083149573 45718187482755015590545)
                ·
                  refine ⟨34288640612066261692909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45718187482755015590545 34288640612066261692909)
                  ·
                    refine ⟨12858240229524848134841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34288640612066261692909 12858240229524848134841)
                    ·
                      rfl

theorem cell22_37562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_37562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37562 prefixEnd_37562 := by exact prefixLift 37562
  have htrace : WordTrace (prefixWord ++ tailWord_37562) baseStart_37562 baseEnd_37562 := by
    simpa [prefixWord, tailWord_37562, baseEnd_37562] using wordTrace_append hprefix tailTrace_37562
  have hstable : (prefixWord ++ tailWord_37562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37562).length < 2 ^ (prefixWord ++ tailWord_37562).sum := by decide
  have hdescent : baseEnd_37562 < baseStart_37562 := by decide
  rcases family_descends (prefixWord ++ tailWord_37562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37564 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_37564 : Nat := 118140960795 + 37564 * 2 ^ 59
def prefixEnd_37564 : Nat := 4983230072969 + 3 ^ 40 * 37564 * 2
def baseEnd_37564 : Nat := 4286308290132503194945

theorem tailTrace_37564 : CollatzResearch.WordTrace tailWord_37564 prefixEnd_37564 4286308290132503194945 := by
  unfold tailWord_37564
  simp only [CollatzResearch.WordTrace]
  refine ⟨685035817959759132775873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 913381090613012177034497 685035817959759132775873)
  ·
    refine ⟨513776863469819349581905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 685035817959759132775873 513776863469819349581905)
    ·
      refine ⟨385332647602364512186429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 513776863469819349581905 385332647602364512186429)
      ·
        refine ⟨144499742850886692069911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385332647602364512186429 144499742850886692069911)
        ·
          refine ⟨216749614276330038104867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144499742850886692069911 216749614276330038104867)
          ·
            refine ⟨325124421414495057157301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216749614276330038104867 325124421414495057157301)
            ·
              refine ⟨30480414507608911608497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 325124421414495057157301 30480414507608911608497)
              ·
                refine ⟨22860310880706683706373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30480414507608911608497 22860310880706683706373)
                ·
                  refine ⟨4286308290132503194945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22860310880706683706373 4286308290132503194945)
                  ·
                    rfl

theorem cell22_37564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_37564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37564 prefixEnd_37564 := by exact prefixLift 37564
  have htrace : WordTrace (prefixWord ++ tailWord_37564) baseStart_37564 baseEnd_37564 := by
    simpa [prefixWord, tailWord_37564, baseEnd_37564] using wordTrace_append hprefix tailTrace_37564
  have hstable : (prefixWord ++ tailWord_37564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37564).length < 2 ^ (prefixWord ++ tailWord_37564).sum := by decide
  have hdescent : baseEnd_37564 < baseStart_37564 := by decide
  rcases family_descends (prefixWord ++ tailWord_37564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37624 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 1, 3]
def baseStart_37624 : Nat := 118140960795 + 37624 * 2 ^ 59
def prefixEnd_37624 : Nat := 4983230072969 + 3 ^ 40 * 37624 * 2
def baseEnd_37624 : Nat := 12879464096577353084651

theorem tailTrace_37624 : CollatzResearch.WordTrace tailWord_37624 prefixEnd_37624 12879464096577353084651 := by
  unfold tailWord_37624
  simp only [CollatzResearch.WordTrace]
  refine ⟨686130007851074256367963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 914840010468099008490617 686130007851074256367963)
  ·
    refine ⟨1029195011776611384551945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686130007851074256367963 1029195011776611384551945)
    ·
      refine ⟨771896258832458538413959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029195011776611384551945 771896258832458538413959)
      ·
        refine ⟨1157844388248687807620939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771896258832458538413959 1157844388248687807620939)
        ·
          refine ⟨1736766582373031711431409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157844388248687807620939 1736766582373031711431409)
          ·
            refine ⟨1302574936779773783573557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736766582373031711431409 1302574936779773783573557)
            ·
              refine ⟨122116400323103792210021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1302574936779773783573557 122116400323103792210021)
              ·
                refine ⟨22896825060581961039379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122116400323103792210021 22896825060581961039379)
                ·
                  refine ⟨34345237590872941559069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22896825060581961039379 34345237590872941559069)
                  ·
                    refine ⟨12879464096577353084651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34345237590872941559069 12879464096577353084651)
                    ·
                      rfl

theorem cell22_37624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_37624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37624 prefixEnd_37624 := by exact prefixLift 37624
  have htrace : WordTrace (prefixWord ++ tailWord_37624) baseStart_37624 baseEnd_37624 := by
    simpa [prefixWord, tailWord_37624, baseEnd_37624] using wordTrace_append hprefix tailTrace_37624
  have hstable : (prefixWord ++ tailWord_37624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37624).length < 2 ^ (prefixWord ++ tailWord_37624).sum := by decide
  have hdescent : baseEnd_37624 < baseStart_37624 := by decide
  rcases family_descends (prefixWord ++ tailWord_37624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37665 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 8]
def baseStart_37665 : Nat := 118140960795 + 37665 * 2 ^ 59
def prefixEnd_37665 : Nat := 4983230072969 + 3 ^ 40 * 37665 * 2
def baseEnd_37665 : Nat := 4297833078155637603175

theorem tailTrace_37665 : CollatzResearch.WordTrace tailWord_37665 prefixEnd_37665 4297833078155637603175 := by
  unfold tailWord_37665
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373755408553612514978449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 915836939035741676652299 1373755408553612514978449)
  ·
    refine ⟨1030316556415209386233837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1373755408553612514978449 1030316556415209386233837)
    ·
      refine ⟨386368708655703519837689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1030316556415209386233837 386368708655703519837689)
      ·
        refine ⟨289776531491777639878267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386368708655703519837689 289776531491777639878267)
        ·
          refine ⟨434664797237666459817401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289776531491777639878267 434664797237666459817401)
          ·
            refine ⟨325998597928249844863051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434664797237666459817401 325998597928249844863051)
            ·
              refine ⟨488997896892374767294577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325998597928249844863051 488997896892374767294577)
              ·
                refine ⟨366748422669281075470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488997896892374767294577 366748422669281075470933)
                ·
                  refine ⟨4297833078155637603175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 366748422669281075470933 4297833078155637603175)
                  ·
                    rfl

theorem cell22_37665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_37665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37665 prefixEnd_37665 := by exact prefixLift 37665
  have htrace : WordTrace (prefixWord ++ tailWord_37665) baseStart_37665 baseEnd_37665 := by
    simpa [prefixWord, tailWord_37665, baseEnd_37665] using wordTrace_append hprefix tailTrace_37665
  have hstable : (prefixWord ++ tailWord_37665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37665).length < 2 ^ (prefixWord ++ tailWord_37665).sum := by decide
  have hdescent : baseEnd_37665 < baseStart_37665 := by decide
  rcases family_descends (prefixWord ++ tailWord_37665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37680 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_37680 : Nat := 118140960795 + 37680 * 2 ^ 59
def prefixEnd_37680 : Nat := 4983230072969 + 3 ^ 40 * 37680 * 2
def baseEnd_37680 : Nat := 12898634041011873684479

theorem tailTrace_37680 : CollatzResearch.WordTrace tailWord_37680 prefixEnd_37680 12898634041011873684479 := by
  unfold tailWord_37680
  simp only [CollatzResearch.WordTrace]
  refine ⟨687151251749635038387247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 916201668999513384516329 687151251749635038387247)
  ·
    refine ⟨1030726877624452557580871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687151251749635038387247 1030726877624452557580871)
    ·
      refine ⟨1546090316436678836371307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030726877624452557580871 1546090316436678836371307)
      ·
        refine ⟨2319135474655018254556961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546090316436678836371307 2319135474655018254556961)
        ·
          refine ⟨1739351605991263690917721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2319135474655018254556961 1739351605991263690917721)
          ·
            refine ⟨1304513704493447768188291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1739351605991263690917721 1304513704493447768188291)
            ·
              refine ⟨1956770556740171652282437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304513704493447768188291 1956770556740171652282437)
              ·
                refine ⟨366894479388782184802957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1956770556740171652282437 366894479388782184802957)
                ·
                  refine ⟨137585429770793319301109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366894479388782184802957 137585429770793319301109)
                  ·
                    refine ⟨12898634041011873684479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137585429770793319301109 12898634041011873684479)
                    ·
                      rfl

theorem cell22_37680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_37680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37680 prefixEnd_37680 := by exact prefixLift 37680
  have htrace : WordTrace (prefixWord ++ tailWord_37680) baseStart_37680 baseEnd_37680 := by
    simpa [prefixWord, tailWord_37680, baseEnd_37680] using wordTrace_append hprefix tailTrace_37680
  have hstable : (prefixWord ++ tailWord_37680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37680).length < 2 ^ (prefixWord ++ tailWord_37680).sum := by decide
  have hdescent : baseEnd_37680 < baseStart_37680 := by decide
  rcases family_descends (prefixWord ++ tailWord_37680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37682 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_37682 : Nat := 118140960795 + 37682 * 2 ^ 59
def prefixEnd_37682 : Nat := 4983230072969 + 3 ^ 40 * 37682 * 2
def baseEnd_37682 : Nat := 4299772893961511711491

theorem tailTrace_37682 : CollatzResearch.WordTrace tailWord_37682 prefixEnd_37682 4299772893961511711491 := by
  unfold tailWord_37682
  simp only [CollatzResearch.WordTrace]
  refine ⟨343593862373006104586825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 916250299661349612231533 343593862373006104586825)
  ·
    refine ⟨257695396779754578440119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 343593862373006104586825 257695396779754578440119)
    ·
      refine ⟨386543095169631867660179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257695396779754578440119 386543095169631867660179)
      ·
        refine ⟨579814642754447801490269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386543095169631867660179 579814642754447801490269)
        ·
          refine ⟨217430491032917925558851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 579814642754447801490269 217430491032917925558851)
          ·
            refine ⟨326145736549376888338277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217430491032917925558851 326145736549376888338277)
            ·
              refine ⟨61152325603008166563427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 326145736549376888338277 61152325603008166563427)
              ·
                refine ⟨91728488404512249845141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61152325603008166563427 91728488404512249845141)
                ·
                  refine ⟨4299772893961511711491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91728488404512249845141 4299772893961511711491)
                  ·
                    rfl

theorem cell22_37682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_37682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37682 prefixEnd_37682 := by exact prefixLift 37682
  have htrace : WordTrace (prefixWord ++ tailWord_37682) baseStart_37682 baseEnd_37682 := by
    simpa [prefixWord, tailWord_37682, baseEnd_37682] using wordTrace_append hprefix tailTrace_37682
  have hstable : (prefixWord ++ tailWord_37682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37682).length < 2 ^ (prefixWord ++ tailWord_37682).sum := by decide
  have hdescent : baseEnd_37682 < baseStart_37682 := by decide
  rcases family_descends (prefixWord ++ tailWord_37682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37789 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 5]
def baseStart_37789 : Nat := 118140960795 + 37789 * 2 ^ 59
def prefixEnd_37789 : Nat := 4983230072969 + 3 ^ 40 * 37789 * 2
def baseEnd_37789 : Nat := 4311982322857307569715

theorem tailTrace_37789 : CollatzResearch.WordTrace tailWord_37789 prefixEnd_37789 4311982322857307569715 := by
  unfold tailWord_37789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378278060104381692492421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 918852040069587794994947 1378278060104381692492421)
  ·
    refine ⟨258427136269571567342329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1378278060104381692492421 258427136269571567342329)
    ·
      refine ⟨193820352202178675506747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258427136269571567342329 193820352202178675506747)
      ·
        refine ⟨290730528303268013260121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193820352202178675506747 290730528303268013260121)
        ·
          refine ⟨218047896227451009945091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290730528303268013260121 218047896227451009945091)
          ·
            refine ⟨327071844341176514917637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218047896227451009945091 327071844341176514917637)
            ·
              refine ⟨61325970813970596547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327071844341176514917637 61325970813970596547057)
              ·
                refine ⟨45994478110477947410293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61325970813970596547057 45994478110477947410293)
                ·
                  refine ⟨4311982322857307569715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45994478110477947410293 4311982322857307569715)
                  ·
                    rfl

theorem cell22_37789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_37789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37789 prefixEnd_37789 := by exact prefixLift 37789
  have htrace : WordTrace (prefixWord ++ tailWord_37789) baseStart_37789 baseEnd_37789 := by
    simpa [prefixWord, tailWord_37789, baseEnd_37789] using wordTrace_append hprefix tailTrace_37789
  have hstable : (prefixWord ++ tailWord_37789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37789).length < 2 ^ (prefixWord ++ tailWord_37789).sum := by decide
  have hdescent : baseEnd_37789 < baseStart_37789 := by decide
  rcases family_descends (prefixWord ++ tailWord_37789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37793 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 1, 3]
def baseStart_37793 : Nat := 118140960795 + 37793 * 2 ^ 59
def prefixEnd_37793 : Nat := 4983230072969 + 3 ^ 40 * 37793 * 2
def baseEnd_37793 : Nat := 12937316250317245609133

theorem tailTrace_37793 : CollatzResearch.WordTrace tailWord_37793 prefixEnd_37793 12937316250317245609133 := by
  unfold tailWord_37793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378423952089890375638033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 918949301393260250425355 1378423952089890375638033)
  ·
    refine ⟨1033817964067417781728525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1378423952089890375638033 1033817964067417781728525)
    ·
      refine ⟨387681736525281668148197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1033817964067417781728525 387681736525281668148197)
      ·
        refine ⟨72690325598490312777787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387681736525281668148197 72690325598490312777787)
        ·
          refine ⟨109035488397735469166681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72690325598490312777787 109035488397735469166681)
          ·
            refine ⟨81776616298301601875011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109035488397735469166681 81776616298301601875011)
            ·
              refine ⟨122664924447452402812517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81776616298301601875011 122664924447452402812517)
              ·
                refine ⟨22999673333897325527347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122664924447452402812517 22999673333897325527347)
                ·
                  refine ⟨34499510000845988291021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22999673333897325527347 34499510000845988291021)
                  ·
                    refine ⟨12937316250317245609133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34499510000845988291021 12937316250317245609133)
                    ·
                      rfl

theorem cell22_37793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_37793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37793 prefixEnd_37793 := by exact prefixLift 37793
  have htrace : WordTrace (prefixWord ++ tailWord_37793) baseStart_37793 baseEnd_37793 := by
    simpa [prefixWord, tailWord_37793, baseEnd_37793] using wordTrace_append hprefix tailTrace_37793
  have hstable : (prefixWord ++ tailWord_37793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37793).length < 2 ^ (prefixWord ++ tailWord_37793).sum := by decide
  have hdescent : baseEnd_37793 < baseStart_37793 := by decide
  rcases family_descends (prefixWord ++ tailWord_37793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37817 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 8]
def baseStart_37817 : Nat := 118140960795 + 37817 * 2 ^ 59
def prefixEnd_37817 : Nat := 4983230072969 + 3 ^ 40 * 37817 * 2
def baseEnd_37817 : Nat := 4315177313596394336353

theorem tailTrace_37817 : CollatzResearch.WordTrace tailWord_37817 prefixEnd_37817 4315177313596394336353 := by
  unfold tailWord_37817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379299304002942474511705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 919532869335294983007803 1379299304002942474511705)
  ·
    refine ⟨1034474478002206855883779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1379299304002942474511705 1034474478002206855883779)
    ·
      refine ⟨1551711717003310283825669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034474478002206855883779 1551711717003310283825669)
      ·
        refine ⟨290945946938120678217313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1551711717003310283825669 290945946938120678217313)
        ·
          refine ⟨218209460203590508662985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290945946938120678217313 218209460203590508662985)
          ·
            refine ⟨163657095152692881497239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218209460203590508662985 163657095152692881497239)
            ·
              refine ⟨245485642729039322245859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163657095152692881497239 245485642729039322245859)
              ·
                refine ⟨368228464093558983368789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245485642729039322245859 368228464093558983368789)
                ·
                  refine ⟨4315177313596394336353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 368228464093558983368789 4315177313596394336353)
                  ·
                    rfl

theorem cell22_37817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_37817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37817 prefixEnd_37817 := by exact prefixLift 37817
  have htrace : WordTrace (prefixWord ++ tailWord_37817) baseStart_37817 baseEnd_37817 := by
    simpa [prefixWord, tailWord_37817, baseEnd_37817] using wordTrace_append hprefix tailTrace_37817
  have hstable : (prefixWord ++ tailWord_37817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37817).length < 2 ^ (prefixWord ++ tailWord_37817).sum := by decide
  have hdescent : baseEnd_37817 < baseStart_37817 := by decide
  rcases family_descends (prefixWord ++ tailWord_37817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37866 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_37866 : Nat := 118140960795 + 37866 * 2 ^ 59
def prefixEnd_37866 : Nat := 4983230072969 + 3 ^ 40 * 37866 * 2
def baseEnd_37866 : Nat := 12962305642169388533909

theorem tailTrace_37866 : CollatzResearch.WordTrace tailWord_37866 prefixEnd_37866 12962305642169388533909 := by
  unfold tailWord_37866
  simp only [CollatzResearch.WordTrace]
  refine ⟨345271620206355960761363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 920724320550282562030301 345271620206355960761363)
  ·
    refine ⟨517907430309533941142045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345271620206355960761363 517907430309533941142045)
    ·
      refine ⟨194215286366075227928267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 517907430309533941142045 194215286366075227928267)
      ·
        refine ⟨291322929549112841892401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194215286366075227928267 291322929549112841892401)
        ·
          refine ⟨218492197161834631419301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291322929549112841892401 218492197161834631419301)
          ·
            refine ⟨40967286967843993391119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218492197161834631419301 40967286967843993391119)
            ·
              refine ⟨61450930451765990086679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40967286967843993391119 61450930451765990086679)
              ·
                refine ⟨92176395677648985130019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61450930451765990086679 92176395677648985130019)
                ·
                  refine ⟨138264593516473477695029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92176395677648985130019 138264593516473477695029)
                  ·
                    refine ⟨12962305642169388533909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 138264593516473477695029 12962305642169388533909)
                    ·
                      rfl

theorem cell22_37866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_37866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37866 prefixEnd_37866 := by exact prefixLift 37866
  have htrace : WordTrace (prefixWord ++ tailWord_37866) baseStart_37866 baseEnd_37866 := by
    simpa [prefixWord, tailWord_37866, baseEnd_37866] using wordTrace_append hprefix tailTrace_37866
  have hstable : (prefixWord ++ tailWord_37866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37866).length < 2 ^ (prefixWord ++ tailWord_37866).sum := by decide
  have hdescent : baseEnd_37866 < baseStart_37866 := by decide
  rcases family_descends (prefixWord ++ tailWord_37866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37917 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_37917 : Nat := 118140960795 + 37917 * 2 ^ 59
def prefixEnd_37917 : Nat := 4983230072969 + 3 ^ 40 * 37917 * 2
def baseEnd_37917 : Nat := 12979763984422255508753

theorem tailTrace_37917 : CollatzResearch.WordTrace tailWord_37917 prefixEnd_37917 12979763984422255508753 := by
  unfold tailWord_37917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382946603640659553152005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 921964402427106368768003 1382946603640659553152005)
  ·
    refine ⟨259302488182623666216001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1382946603640659553152005 259302488182623666216001)
    ·
      refine ⟨194476866136967749662001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259302488182623666216001 194476866136967749662001)
      ·
        refine ⟨145857649602725812246501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194476866136967749662001 145857649602725812246501)
        ·
          refine ⟨27348309300511089796219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145857649602725812246501 27348309300511089796219)
          ·
            refine ⟨41022463950766634694329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27348309300511089796219 41022463950766634694329)
            ·
              refine ⟨30766847963074976020747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41022463950766634694329 30766847963074976020747)
              ·
                refine ⟨46150271944612464031121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30766847963074976020747 46150271944612464031121)
                ·
                  refine ⟨34612703958459348023341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46150271944612464031121 34612703958459348023341)
                  ·
                    refine ⟨12979763984422255508753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34612703958459348023341 12979763984422255508753)
                    ·
                      rfl

theorem cell22_37917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_37917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37917 prefixEnd_37917 := by exact prefixLift 37917
  have htrace : WordTrace (prefixWord ++ tailWord_37917) baseStart_37917 baseEnd_37917 := by
    simpa [prefixWord, tailWord_37917, baseEnd_37917] using wordTrace_append hprefix tailTrace_37917
  have hstable : (prefixWord ++ tailWord_37917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37917).length < 2 ^ (prefixWord ++ tailWord_37917).sum := by decide
  have hdescent : baseEnd_37917 < baseStart_37917 := by decide
  rcases family_descends (prefixWord ++ tailWord_37917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37958 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_37958 : Nat := 118140960795 + 37958 * 2 ^ 59
def prefixEnd_37958 : Nat := 4983230072969 + 3 ^ 40 * 37958 * 2
def baseEnd_37958 : Nat := 4331266374103938411209

theorem tailTrace_37958 : CollatzResearch.WordTrace tailWord_37958 prefixEnd_37958 4331266374103938411209 := by
  unfold tailWord_37958
  simp only [CollatzResearch.WordTrace]
  refine ⟨43263812390378861106079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 922961330994749036929685 43263812390378861106079)
  ·
    refine ⟨64895718585568291659119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43263812390378861106079 64895718585568291659119)
    ·
      refine ⟨97343577878352437488679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64895718585568291659119 97343577878352437488679)
      ·
        refine ⟨146015366817528656233019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97343577878352437488679 146015366817528656233019)
        ·
          refine ⟨219023050226292984349529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146015366817528656233019 219023050226292984349529)
          ·
            refine ⟨164267287669719738262147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219023050226292984349529 164267287669719738262147)
            ·
              refine ⟨246400931504579607393221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164267287669719738262147 246400931504579607393221)
              ·
                refine ⟨46200174657108676386229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246400931504579607393221 46200174657108676386229)
                ·
                  refine ⟨4331266374103938411209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46200174657108676386229 4331266374103938411209)
                  ·
                    rfl

theorem cell22_37958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_37958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37958 prefixEnd_37958 := by exact prefixLift 37958
  have htrace : WordTrace (prefixWord ++ tailWord_37958) baseStart_37958 baseEnd_37958 := by
    simpa [prefixWord, tailWord_37958, baseEnd_37958] using wordTrace_append hprefix tailTrace_37958
  have hstable : (prefixWord ++ tailWord_37958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37958).length < 2 ^ (prefixWord ++ tailWord_37958).sum := by decide
  have hdescent : baseEnd_37958 < baseStart_37958 := by decide
  rcases family_descends (prefixWord ++ tailWord_37958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37986 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_37986 : Nat := 118140960795 + 37986 * 2 ^ 59
def prefixEnd_37986 : Nat := 4983230072969 + 3 ^ 40 * 37986 * 2
def baseEnd_37986 : Nat := 4334461364843025177847

theorem tailTrace_37986 : CollatzResearch.WordTrace tailWord_37986 prefixEnd_37986 4334461364843025177847 := by
  unfold tailWord_37986
  simp only [CollatzResearch.WordTrace]
  refine ⟨346365810097671084353453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 923642160260456224942541 346365810097671084353453)
  ·
    refine ⟨129887178786626656632545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 346365810097671084353453 129887178786626656632545)
    ·
      refine ⟨97415384089969992474409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129887178786626656632545 97415384089969992474409)
      ·
        refine ⟨73061538067477494355807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97415384089969992474409 73061538067477494355807)
        ·
          refine ⟨109592307101216241533711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73061538067477494355807 109592307101216241533711)
          ·
            refine ⟨164388460651824362300567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109592307101216241533711 164388460651824362300567)
            ·
              refine ⟨246582690977736543450851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164388460651824362300567 246582690977736543450851)
              ·
                refine ⟨369874036466604815176277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246582690977736543450851 369874036466604815176277)
                ·
                  refine ⟨4334461364843025177847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 369874036466604815176277 4334461364843025177847)
                  ·
                    rfl

theorem cell22_37986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_37986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37986 prefixEnd_37986 := by exact prefixLift 37986
  have htrace : WordTrace (prefixWord ++ tailWord_37986) baseStart_37986 baseEnd_37986 := by
    simpa [prefixWord, tailWord_37986, baseEnd_37986] using wordTrace_append hprefix tailTrace_37986
  have hstable : (prefixWord ++ tailWord_37986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37986).length < 2 ^ (prefixWord ++ tailWord_37986).sum := by decide
  have hdescent : baseEnd_37986 < baseStart_37986 := by decide
  rcases family_descends (prefixWord ++ tailWord_37986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37999 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_37999 : Nat := 118140960795 + 37999 * 2 ^ 59
def prefixEnd_37999 : Nat := 4983230072969 + 3 ^ 40 * 37999 * 2
def baseEnd_37999 : Nat := 13007834260201374958501

theorem tailTrace_37999 : CollatzResearch.WordTrace tailWord_37999 prefixEnd_37999 13007834260201374958501 := by
  unfold tailWord_37999
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385937389343587557637051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 923958259562391705091367 1385937389343587557637051)
  ·
    refine ⟨2078906084015381336455577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385937389343587557637051 2078906084015381336455577)
    ·
      refine ⟨1559179563011536002341683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078906084015381336455577 1559179563011536002341683)
      ·
        refine ⟨2338769344517304003512525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559179563011536002341683 2338769344517304003512525)
        ·
          refine ⟨877038504193989001317197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338769344517304003512525 877038504193989001317197)
          ·
            refine ⟨328889439072745875493949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 877038504193989001317197 328889439072745875493949)
            ·
              refine ⟨123333539652279703310231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328889439072745875493949 123333539652279703310231)
              ·
                refine ⟨185000309478419554965347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123333539652279703310231 185000309478419554965347)
                ·
                  refine ⟨277500464217629332448021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185000309478419554965347 277500464217629332448021)
                  ·
                    refine ⟨13007834260201374958501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 277500464217629332448021 13007834260201374958501)
                    ·
                      rfl

theorem cell22_37999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_37999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_37999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_37999 prefixEnd_37999 := by exact prefixLift 37999
  have htrace : WordTrace (prefixWord ++ tailWord_37999) baseStart_37999 baseEnd_37999 := by
    simpa [prefixWord, tailWord_37999, baseEnd_37999] using wordTrace_append hprefix tailTrace_37999
  have hstable : (prefixWord ++ tailWord_37999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37999).length < 2 ^ (prefixWord ++ tailWord_37999).sum := by decide
  have hdescent : baseEnd_37999 < baseStart_37999 := by decide
  rcases family_descends (prefixWord ++ tailWord_37999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38005 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_38005 : Nat := 118140960795 + 38005 * 2 ^ 59
def prefixEnd_38005 : Nat := 4983230072969 + 3 ^ 40 * 38005 * 2
def baseEnd_38005 : Nat := 13009888182819359308483

theorem tailTrace_38005 : CollatzResearch.WordTrace tailWord_38005 prefixEnd_38005 13009888182819359308483 := by
  unfold tailWord_38005
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386156227321850582355469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 924104151547900388236979 1386156227321850582355469)
  ·
    refine ⟨519808585245693968383301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1386156227321850582355469 519808585245693968383301)
    ·
      refine ⟨97464109733567619071869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 519808585245693968383301 97464109733567619071869)
      ·
        refine ⟨36549041150087857151951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97464109733567619071869 36549041150087857151951)
        ·
          refine ⟨54823561725131785727927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36549041150087857151951 54823561725131785727927)
          ·
            refine ⟨82235342587697678591891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54823561725131785727927 82235342587697678591891)
            ·
              refine ⟨123353013881546517887837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82235342587697678591891 123353013881546517887837)
              ·
                refine ⟨46257380205579944207939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123353013881546517887837 46257380205579944207939)
                ·
                  refine ⟨69386070308369916311909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46257380205579944207939 69386070308369916311909)
                  ·
                    refine ⟨13009888182819359308483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69386070308369916311909 13009888182819359308483)
                    ·
                      rfl

theorem cell22_38005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_38005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38005 prefixEnd_38005 := by exact prefixLift 38005
  have htrace : WordTrace (prefixWord ++ tailWord_38005) baseStart_38005 baseEnd_38005 := by
    simpa [prefixWord, tailWord_38005, baseEnd_38005] using wordTrace_append hprefix tailTrace_38005
  have hstable : (prefixWord ++ tailWord_38005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38005).length < 2 ^ (prefixWord ++ tailWord_38005).sum := by decide
  have hdescent : baseEnd_38005 < baseStart_38005 := by decide
  rcases family_descends (prefixWord ++ tailWord_38005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38076 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_38076 : Nat := 118140960795 + 38076 * 2 ^ 59
def prefixEnd_38076 : Nat := 4983230072969 + 3 ^ 40 * 38076 * 2
def baseEnd_38076 : Nat := 4344730977932946927755

theorem tailTrace_38076 : CollatzResearch.WordTrace tailWord_38076 prefixEnd_38076 4344730977932946927755 := by
  unfold tailWord_38076
  simp only [CollatzResearch.WordTrace]
  refine ⟨694372905032314854095041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 925830540043086472126721 694372905032314854095041)
  ·
    refine ⟨520779678774236140571281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 694372905032314854095041 520779678774236140571281)
    ·
      refine ⟨390584759080677105428461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520779678774236140571281 390584759080677105428461)
      ·
        refine ⟨146469284655253914535673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 390584759080677105428461 146469284655253914535673)
        ·
          refine ⟨109851963491440435901755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146469284655253914535673 109851963491440435901755)
          ·
            refine ⟨164777945237160653852633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109851963491440435901755 164777945237160653852633)
            ·
              refine ⟨123583458927870490389475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164777945237160653852633 123583458927870490389475)
              ·
                refine ⟨185375188391805735584213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123583458927870490389475 185375188391805735584213)
                ·
                  refine ⟨4344730977932946927755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 185375188391805735584213 4344730977932946927755)
                  ·
                    rfl

theorem cell22_38076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_38076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38076 prefixEnd_38076 := by exact prefixLift 38076
  have htrace : WordTrace (prefixWord ++ tailWord_38076) baseStart_38076 baseEnd_38076 := by
    simpa [prefixWord, tailWord_38076, baseEnd_38076] using wordTrace_append hprefix tailTrace_38076
  have hstable : (prefixWord ++ tailWord_38076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38076).length < 2 ^ (prefixWord ++ tailWord_38076).sum := by decide
  have hdescent : baseEnd_38076 < baseStart_38076 := by decide
  rcases family_descends (prefixWord ++ tailWord_38076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38080 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_38080 : Nat := 118140960795 + 38080 * 2 ^ 59
def prefixEnd_38080 : Nat := 4983230072969 + 3 ^ 40 * 38080 * 2
def baseEnd_38080 : Nat := 13035562215544163683253

theorem tailTrace_38080 : CollatzResearch.WordTrace tailWord_38080 prefixEnd_38080 13035562215544163683253 := by
  unfold tailWord_38080
  simp only [CollatzResearch.WordTrace]
  refine ⟨694445851025069195667847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 925927801366758927557129 694445851025069195667847)
  ·
    refine ⟨1041668776537603793501771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 694445851025069195667847 1041668776537603793501771)
    ·
      refine ⟨1562503164806405690252657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041668776537603793501771 1562503164806405690252657)
      ·
        refine ⟨1171877373604804267689493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562503164806405690252657 1171877373604804267689493)
        ·
          refine ⟨54931751887725200047945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1171877373604804267689493 54931751887725200047945)
          ·
            refine ⟨41198813915793900035959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54931751887725200047945 41198813915793900035959)
            ·
              refine ⟨61798220873690850053939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41198813915793900035959 61798220873690850053939)
              ·
                refine ⟨92697331310536275080909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61798220873690850053939 92697331310536275080909)
                ·
                  refine ⟨34761499241451103155341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92697331310536275080909 34761499241451103155341)
                  ·
                    refine ⟨13035562215544163683253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34761499241451103155341 13035562215544163683253)
                    ·
                      rfl

theorem cell22_38080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_38080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38080 prefixEnd_38080 := by exact prefixLift 38080
  have htrace : WordTrace (prefixWord ++ tailWord_38080) baseStart_38080 baseEnd_38080 := by
    simpa [prefixWord, tailWord_38080, baseEnd_38080] using wordTrace_append hprefix tailTrace_38080
  have hstable : (prefixWord ++ tailWord_38080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38080).length < 2 ^ (prefixWord ++ tailWord_38080).sum := by decide
  have hdescent : baseEnd_38080 < baseStart_38080 := by decide
  rcases family_descends (prefixWord ++ tailWord_38080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38138 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_38138 : Nat := 118140960795 + 38138 * 2 ^ 59
def prefixEnd_38138 : Nat := 4983230072969 + 3 ^ 40 * 38138 * 2
def baseEnd_38138 : Nat := 4351805600283781911025

theorem tailTrace_38138 : CollatzResearch.WordTrace tailWord_38138 prefixEnd_38138 4351805600283781911025 := by
  unfold tailWord_38138
  simp only [CollatzResearch.WordTrace]
  refine ⟨347751783960003574236767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 927338090560009531298045 347751783960003574236767)
  ·
    refine ⟨521627675940005361355151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347751783960003574236767 521627675940005361355151)
    ·
      refine ⟨782441513910008042032727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521627675940005361355151 782441513910008042032727)
      ·
        refine ⟨1173662270865012063049091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782441513910008042032727 1173662270865012063049091)
        ·
          refine ⟨1760493406297518094573637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173662270865012063049091 1760493406297518094573637)
          ·
            refine ⟨330092513680784642732557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1760493406297518094573637 330092513680784642732557)
            ·
              refine ⟨123784692630294241024709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330092513680784642732557 123784692630294241024709)
              ·
                refine ⟨23209629868180170192133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123784692630294241024709 23209629868180170192133)
                ·
                  refine ⟨4351805600283781911025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23209629868180170192133 4351805600283781911025)
                  ·
                    rfl

theorem cell22_38138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_38138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38138 prefixEnd_38138 := by exact prefixLift 38138
  have htrace : WordTrace (prefixWord ++ tailWord_38138) baseStart_38138 baseEnd_38138 := by
    simpa [prefixWord, tailWord_38138, baseEnd_38138] using wordTrace_append hprefix tailTrace_38138
  have hstable : (prefixWord ++ tailWord_38138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38138).length < 2 ^ (prefixWord ++ tailWord_38138).sum := by decide
  have hdescent : baseEnd_38138 < baseStart_38138 := by decide
  rcases family_descends (prefixWord ++ tailWord_38138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38153 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_38153 : Nat := 118140960795 + 38153 * 2 ^ 59
def prefixEnd_38153 : Nat := 4983230072969 + 3 ^ 40 * 38153 * 2
def baseEnd_38153 : Nat := 13060551607396306608029

theorem tailTrace_38153 : CollatzResearch.WordTrace tailWord_38153 prefixEnd_38153 13060551607396306608029 := by
  unfold tailWord_38153
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391554230785671858743113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 927702820523781239162075 1391554230785671858743113)
  ·
    refine ⟨1043665673089253894057335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391554230785671858743113 1043665673089253894057335)
    ·
      refine ⟨1565498509633880841086003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043665673089253894057335 1565498509633880841086003)
      ·
        refine ⟨2348247764450821261629005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565498509633880841086003 2348247764450821261629005)
        ·
          refine ⟨880592911669057973110877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2348247764450821261629005 880592911669057973110877)
          ·
            refine ⟨330222341875896739916579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 880592911669057973110877 330222341875896739916579)
            ·
              refine ⟨495333512813845109874869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330222341875896739916579 495333512813845109874869)
              ·
                refine ⟨46437516826297979050769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 495333512813845109874869 46437516826297979050769)
                ·
                  refine ⟨34828137619723484288077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46437516826297979050769 34828137619723484288077)
                  ·
                    refine ⟨13060551607396306608029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34828137619723484288077 13060551607396306608029)
                    ·
                      rfl

theorem cell22_38153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_38153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38153 prefixEnd_38153 := by exact prefixLift 38153
  have htrace : WordTrace (prefixWord ++ tailWord_38153) baseStart_38153 baseEnd_38153 := by
    simpa [prefixWord, tailWord_38153, baseEnd_38153] using wordTrace_append hprefix tailTrace_38153
  have hstable : (prefixWord ++ tailWord_38153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38153).length < 2 ^ (prefixWord ++ tailWord_38153).sum := by decide
  have hdescent : baseEnd_38153 < baseStart_38153 := by decide
  rcases family_descends (prefixWord ++ tailWord_38153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38168 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_38168 : Nat := 118140960795 + 38168 * 2 ^ 59
def prefixEnd_38168 : Nat := 4983230072969 + 3 ^ 40 * 38168 * 2
def baseEnd_38168 : Nat := 13065686413941267482983

theorem tailTrace_38168 : CollatzResearch.WordTrace tailWord_38168 prefixEnd_38168 13065686413941267482983 := by
  unfold tailWord_38168
  simp only [CollatzResearch.WordTrace]
  refine ⟨696050662865664710269579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 928067550487552947026105 696050662865664710269579)
  ·
    refine ⟨1044075994298497065404369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696050662865664710269579 1044075994298497065404369)
    ·
      refine ⟨783056995723872799053277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1044075994298497065404369 783056995723872799053277)
      ·
        refine ⟨293646373396452299644979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 783056995723872799053277 293646373396452299644979)
        ·
          refine ⟨440469560094678449467469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293646373396452299644979 440469560094678449467469)
          ·
            refine ⟨165176085035504418550301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440469560094678449467469 165176085035504418550301)
            ·
              refine ⟨61941031888314156956363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165176085035504418550301 61941031888314156956363)
              ·
                refine ⟨92911547832471235434545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61941031888314156956363 92911547832471235434545)
                ·
                  refine ⟨69683660874353426575909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92911547832471235434545 69683660874353426575909)
                  ·
                    refine ⟨13065686413941267482983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69683660874353426575909 13065686413941267482983)
                    ·
                      rfl

theorem cell22_38168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_38168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38168 prefixEnd_38168 := by exact prefixLift 38168
  have htrace : WordTrace (prefixWord ++ tailWord_38168) baseStart_38168 baseEnd_38168 := by
    simpa [prefixWord, tailWord_38168, baseEnd_38168] using wordTrace_append hprefix tailTrace_38168
  have hstable : (prefixWord ++ tailWord_38168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38168).length < 2 ^ (prefixWord ++ tailWord_38168).sum := by decide
  have hdescent : baseEnd_38168 < baseStart_38168 := by decide
  rcases family_descends (prefixWord ++ tailWord_38168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38258 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_38258 : Nat := 118140960795 + 38258 * 2 ^ 59
def prefixEnd_38258 : Nat := 4983230072969 + 3 ^ 40 * 38258 * 2
def baseEnd_38258 : Nat := 13096495253211032732707

theorem tailTrace_38258 : CollatzResearch.WordTrace tailWord_38258 prefixEnd_38258 13096495253211032732707 := by
  unfold tailWord_38258
  simp only [CollatzResearch.WordTrace]
  refine ⟨348845973851318697828857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 930255930270183194210285 348845973851318697828857)
  ·
    refine ⟨261634480388489023371643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 348845973851318697828857 261634480388489023371643)
    ·
      refine ⟨392451720582733535057465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261634480388489023371643 392451720582733535057465)
      ·
        refine ⟨294338790437050151293099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392451720582733535057465 294338790437050151293099)
        ·
          refine ⟨441508185655575226939649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294338790437050151293099 441508185655575226939649)
          ·
            refine ⟨331131139241681420204737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441508185655575226939649 331131139241681420204737)
            ·
              refine ⟨248348354431261065153553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331131139241681420204737 248348354431261065153553)
              ·
                refine ⟨186261265823445798865165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248348354431261065153553 186261265823445798865165)
                ·
                  refine ⟨69847974683792174574437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186261265823445798865165 69847974683792174574437)
                  ·
                    refine ⟨13096495253211032732707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69847974683792174574437 13096495253211032732707)
                    ·
                      rfl

theorem cell22_38258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_38258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38258 prefixEnd_38258 := by exact prefixLift 38258
  have htrace : WordTrace (prefixWord ++ tailWord_38258) baseStart_38258 baseEnd_38258 := by
    simpa [prefixWord, tailWord_38258, baseEnd_38258] using wordTrace_append hprefix tailTrace_38258
  have hstable : (prefixWord ++ tailWord_38258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38258).length < 2 ^ (prefixWord ++ tailWord_38258).sum := by decide
  have hdescent : baseEnd_38258 < baseStart_38258 := by decide
  rcases family_descends (prefixWord ++ tailWord_38258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38275 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 1, 4]
def baseStart_38275 : Nat := 118140960795 + 38275 * 2 ^ 59
def prefixEnd_38275 : Nat := 4983230072969 + 3 ^ 40 * 38275 * 2
def baseEnd_38275 : Nat := 13102314700628655057655

theorem tailTrace_38275 : CollatzResearch.WordTrace tailWord_38275 prefixEnd_38275 13102314700628655057655 := by
  unfold tailWord_38275
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396003936343686694684279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 930669290895791129789519 1396003936343686694684279)
  ·
    refine ⟨2094005904515530042026419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1396003936343686694684279 2094005904515530042026419)
    ·
      refine ⟨3141008856773295063039629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094005904515530042026419 3141008856773295063039629)
      ·
        refine ⟨1177878321289985648639861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3141008856773295063039629 1177878321289985648639861)
        ·
          refine ⟨110426092620936154559987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1177878321289985648639861 110426092620936154559987)
          ·
            refine ⟨165639138931404231839981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110426092620936154559987 165639138931404231839981)
            ·
              refine ⟨62114677099276586939993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165639138931404231839981 62114677099276586939993)
              ·
                refine ⟨46586007824457440204995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62114677099276586939993 46586007824457440204995)
                ·
                  refine ⟨69879011736686160307493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46586007824457440204995 69879011736686160307493)
                  ·
                    refine ⟨13102314700628655057655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69879011736686160307493 13102314700628655057655)
                    ·
                      rfl

theorem cell22_38275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4].length) (baseStart_38275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38275 prefixEnd_38275 := by exact prefixLift 38275
  have htrace : WordTrace (prefixWord ++ tailWord_38275) baseStart_38275 baseEnd_38275 := by
    simpa [prefixWord, tailWord_38275, baseEnd_38275] using wordTrace_append hprefix tailTrace_38275
  have hstable : (prefixWord ++ tailWord_38275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38275).length < 2 ^ (prefixWord ++ tailWord_38275).sum := by decide
  have hdescent : baseEnd_38275 < baseStart_38275 := by decide
  rcases family_descends (prefixWord ++ tailWord_38275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38356 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_38356 : Nat := 118140960795 + 38356 * 2 ^ 59
def prefixEnd_38356 : Nat := 4983230072969 + 3 ^ 40 * 38356 * 2
def baseEnd_38356 : Nat := 13130042655971443782407

theorem tailTrace_38356 : CollatzResearch.WordTrace tailWord_38356 prefixEnd_38356 13130042655971443782407 := by
  unfold tailWord_38356
  simp only [CollatzResearch.WordTrace]
  refine ⟨699479124525118764191461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 932638832700158352255281 699479124525118764191461)
  ·
    refine ⟨131152335848459768285899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 699479124525118764191461 131152335848459768285899)
    ·
      refine ⟨196728503772689652428849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131152335848459768285899 196728503772689652428849)
      ·
        refine ⟨147546377829517239321637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196728503772689652428849 147546377829517239321637)
        ·
          refine ⟨27664945843034482372807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147546377829517239321637 27664945843034482372807)
          ·
            refine ⟨41497418764551723559211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27664945843034482372807 41497418764551723559211)
            ·
              refine ⟨62246128146827585338817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41497418764551723559211 62246128146827585338817)
              ·
                refine ⟨46684596110120689004113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62246128146827585338817 46684596110120689004113)
                ·
                  refine ⟨35013447082590516753085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46684596110120689004113 35013447082590516753085)
                  ·
                    refine ⟨13130042655971443782407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35013447082590516753085 13130042655971443782407)
                    ·
                      rfl

theorem cell22_38356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_38356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38356 prefixEnd_38356 := by exact prefixLift 38356
  have htrace : WordTrace (prefixWord ++ tailWord_38356) baseStart_38356 baseEnd_38356 := by
    simpa [prefixWord, tailWord_38356, baseEnd_38356] using wordTrace_append hprefix tailTrace_38356
  have hstable : (prefixWord ++ tailWord_38356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38356).length < 2 ^ (prefixWord ++ tailWord_38356).sum := by decide
  have hdescent : baseEnd_38356 < baseStart_38356 := by decide
  rcases family_descends (prefixWord ++ tailWord_38356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38367 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 1, 3]
def baseStart_38367 : Nat := 118140960795 + 38367 * 2 ^ 59
def prefixEnd_38367 : Nat := 4983230072969 + 3 ^ 40 * 38367 * 2
def baseEnd_38367 : Nat := 13133808180771081757373

theorem tailTrace_38367 : CollatzResearch.WordTrace tailWord_38367 prefixEnd_38367 13133808180771081757373 := by
  unfold tailWord_38367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399359452010386407033355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 932906301340257604688903 1399359452010386407033355)
  ·
    refine ⟨2099039178015579610550033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1399359452010386407033355 2099039178015579610550033)
    ·
      refine ⟨1574279383511684707912525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2099039178015579610550033 1574279383511684707912525)
      ·
        refine ⟨590354768816881765467197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1574279383511684707912525 590354768816881765467197)
        ·
          refine ⟨221383038306330662050199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590354768816881765467197 221383038306330662050199)
          ·
            refine ⟨332074557459495993075299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221383038306330662050199 332074557459495993075299)
            ·
              refine ⟨498111836189243989612949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332074557459495993075299 498111836189243989612949)
              ·
                refine ⟨23348992321370812013107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 498111836189243989612949 23348992321370812013107)
                ·
                  refine ⟨35023488482056218019661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23348992321370812013107 35023488482056218019661)
                  ·
                    refine ⟨13133808180771081757373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35023488482056218019661 13133808180771081757373)
                    ·
                      rfl

theorem cell22_38367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_38367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38367 prefixEnd_38367 := by exact prefixLift 38367
  have htrace : WordTrace (prefixWord ++ tailWord_38367) baseStart_38367 baseEnd_38367 := by
    simpa [prefixWord, tailWord_38367, baseEnd_38367] using wordTrace_append hprefix tailTrace_38367
  have hstable : (prefixWord ++ tailWord_38367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38367).length < 2 ^ (prefixWord ++ tailWord_38367).sum := by decide
  have hdescent : baseEnd_38367 < baseStart_38367 := by decide
  rcases family_descends (prefixWord ++ tailWord_38367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38401 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 1, 3]
def baseStart_38401 : Nat := 118140960795 + 38401 * 2 ^ 59
def prefixEnd_38401 : Nat := 4983230072969 + 3 ^ 40 * 38401 * 2
def baseEnd_38401 : Nat := 13145447075606326407269

theorem tailTrace_38401 : CollatzResearch.WordTrace tailWord_38401 prefixEnd_38401 13145447075606326407269 := by
  unfold tailWord_38401
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400599533887210213771057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 933733022591473475847371 1400599533887210213771057)
  ·
    refine ⟨1050449650415407660328293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1400599533887210213771057 1050449650415407660328293)
    ·
      refine ⟨196959309452888936311555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1050449650415407660328293 196959309452888936311555)
      ·
        refine ⟨295438964179333404467333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196959309452888936311555 295438964179333404467333)
        ·
          refine ⟨55394805783625013337625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295438964179333404467333 55394805783625013337625)
          ·
            refine ⟨41546104337718760003219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55394805783625013337625 41546104337718760003219)
            ·
              refine ⟨62319156506578140004829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41546104337718760003219 62319156506578140004829)
              ·
                refine ⟨23369683689966802501811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62319156506578140004829 23369683689966802501811)
                ·
                  refine ⟨35054525534950203752717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23369683689966802501811 35054525534950203752717)
                  ·
                    refine ⟨13145447075606326407269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35054525534950203752717 13145447075606326407269)
                    ·
                      rfl

theorem cell22_38401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_38401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38401 prefixEnd_38401 := by exact prefixLift 38401
  have htrace : WordTrace (prefixWord ++ tailWord_38401) baseStart_38401 baseEnd_38401 := by
    simpa [prefixWord, tailWord_38401, baseEnd_38401] using wordTrace_append hprefix tailTrace_38401
  have hstable : (prefixWord ++ tailWord_38401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38401).length < 2 ^ (prefixWord ++ tailWord_38401).sum := by decide
  have hdescent : baseEnd_38401 < baseStart_38401 := by decide
  rcases family_descends (prefixWord ++ tailWord_38401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38408 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_38408 : Nat := 118140960795 + 38408 * 2 ^ 59
def prefixEnd_38408 : Nat := 4983230072969 + 3 ^ 40 * 38408 * 2
def baseEnd_38408 : Nat := 4382614439553547160749

theorem tailTrace_38408 : CollatzResearch.WordTrace tailWord_38408 prefixEnd_38408 4382614439553547160749 := by
  unfold tailWord_38408
  simp only [CollatzResearch.WordTrace]
  refine ⟨700427422430925204637939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 933903229907900272850585 700427422430925204637939)
  ·
    refine ⟨1050641133646387806956909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 700427422430925204637939 1050641133646387806956909)
    ·
      refine ⟨393990425117395427608841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1050641133646387806956909 393990425117395427608841)
      ·
        refine ⟨295492818838046570706631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393990425117395427608841 295492818838046570706631)
        ·
          refine ⟨443239228257069856059947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295492818838046570706631 443239228257069856059947)
          ·
            refine ⟨664858842385604784089921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443239228257069856059947 664858842385604784089921)
            ·
              refine ⟨498644131789203588067441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664858842385604784089921 498644131789203588067441)
              ·
                refine ⟨373983098841902691050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498644131789203588067441 373983098841902691050581)
                ·
                  refine ⟨4382614439553547160749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 373983098841902691050581 4382614439553547160749)
                  ·
                    rfl

theorem cell22_38408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_38408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38408 prefixEnd_38408 := by exact prefixLift 38408
  have htrace : WordTrace (prefixWord ++ tailWord_38408) baseStart_38408 baseEnd_38408 := by
    simpa [prefixWord, tailWord_38408, baseEnd_38408] using wordTrace_append hprefix tailTrace_38408
  have hstable : (prefixWord ++ tailWord_38408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38408).length < 2 ^ (prefixWord ++ tailWord_38408).sum := by decide
  have hdescent : baseEnd_38408 < baseStart_38408 := by decide
  rcases family_descends (prefixWord ++ tailWord_38408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38455 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_38455 : Nat := 118140960795 + 38455 * 2 ^ 59
def prefixEnd_38455 : Nat := 4983230072969 + 3 ^ 40 * 38455 * 2
def baseEnd_38455 : Nat := 13163932379168185557103

theorem tailTrace_38455 : CollatzResearch.WordTrace tailWord_38455 prefixEnd_38455 13163932379168185557103 := by
  unfold tailWord_38455
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402569075691577436236819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 935046050461051624157879 1402569075691577436236819)
  ·
    refine ⟨2103853613537366154355229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402569075691577436236819 2103853613537366154355229)
    ·
      refine ⟨788945105076512307883211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2103853613537366154355229 788945105076512307883211)
      ·
        refine ⟨1183417657614768461824817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788945105076512307883211 1183417657614768461824817)
        ·
          refine ⟨887563243211076346368613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1183417657614768461824817 887563243211076346368613)
          ·
            refine ⟨166418108102076814944115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 887563243211076346368613 166418108102076814944115)
            ·
              refine ⟨249627162153115222416173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166418108102076814944115 249627162153115222416173)
              ·
                refine ⟨93610185807418208406065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249627162153115222416173 93610185807418208406065)
                ·
                  refine ⟨70207639355563656304549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93610185807418208406065 70207639355563656304549)
                  ·
                    refine ⟨13163932379168185557103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70207639355563656304549 13163932379168185557103)
                    ·
                      rfl

theorem cell22_38455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_38455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38455 prefixEnd_38455 := by exact prefixLift 38455
  have htrace : WordTrace (prefixWord ++ tailWord_38455) baseStart_38455 baseEnd_38455 := by
    simpa [prefixWord, tailWord_38455, baseEnd_38455] using wordTrace_append hprefix tailTrace_38455
  have hstable : (prefixWord ++ tailWord_38455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38455).length < 2 ^ (prefixWord ++ tailWord_38455).sum := by decide
  have hdescent : baseEnd_38455 < baseStart_38455 := by decide
  rcases family_descends (prefixWord ++ tailWord_38455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38532 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_38532 : Nat := 118140960795 + 38532 * 2 ^ 59
def prefixEnd_38532 : Nat := 4983230072969 + 3 ^ 40 * 38532 * 2
def baseEnd_38532 : Nat := 4396763684255217127289

theorem tailTrace_38532 : CollatzResearch.WordTrace tailWord_38532 prefixEnd_38532 4396763684255217127289 := by
  unfold tailWord_38532
  simp only [CollatzResearch.WordTrace]
  refine ⟨702688748206309793394925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 936918330941746391193233 702688748206309793394925)
  ·
    refine ⟨263508280577366172523097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 702688748206309793394925 263508280577366172523097)
    ·
      refine ⟨197631210433024629392323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263508280577366172523097 197631210433024629392323)
      ·
        refine ⟨296446815649536944088485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197631210433024629392323 296446815649536944088485)
        ·
          refine ⟨55583777934288177016591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296446815649536944088485 55583777934288177016591)
          ·
            refine ⟨83375666901432265524887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55583777934288177016591 83375666901432265524887)
            ·
              refine ⟨125063500352148398287331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83375666901432265524887 125063500352148398287331)
              ·
                refine ⟨187595250528222597430997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125063500352148398287331 187595250528222597430997)
                ·
                  refine ⟨4396763684255217127289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 187595250528222597430997 4396763684255217127289)
                  ·
                    rfl

theorem cell22_38532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_38532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38532 prefixEnd_38532 := by exact prefixLift 38532
  have htrace : WordTrace (prefixWord ++ tailWord_38532) baseStart_38532 baseEnd_38532 := by
    simpa [prefixWord, tailWord_38532, baseEnd_38532] using wordTrace_append hprefix tailTrace_38532
  have hstable : (prefixWord ++ tailWord_38532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38532).length < 2 ^ (prefixWord ++ tailWord_38532).sum := by decide
  have hdescent : baseEnd_38532 < baseStart_38532 := by decide
  rcases family_descends (prefixWord ++ tailWord_38532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38536 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_38536 : Nat := 118140960795 + 38536 * 2 ^ 59
def prefixEnd_38536 : Nat := 4983230072969 + 3 ^ 40 * 38536 * 2
def baseEnd_38536 : Nat := 13191660334510974281855

theorem tailTrace_38536 : CollatzResearch.WordTrace tailWord_38536 prefixEnd_38536 13191660334510974281855 := by
  unfold tailWord_38536
  simp only [CollatzResearch.WordTrace]
  refine ⟨702761694199064134967731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 937015592265418846623641 702761694199064134967731)
  ·
    refine ⟨1054142541298596202451597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702761694199064134967731 1054142541298596202451597)
    ·
      refine ⟨395303452986973575919349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1054142541298596202451597 395303452986973575919349)
      ·
        refine ⟨37059698717528772742439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 395303452986973575919349 37059698717528772742439)
        ·
          refine ⟨55589548076293159113659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37059698717528772742439 55589548076293159113659)
          ·
            refine ⟨83384322114439738670489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55589548076293159113659 83384322114439738670489)
            ·
              refine ⟨62538241585829804002867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83384322114439738670489 62538241585829804002867)
              ·
                refine ⟨93807362378744706004301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62538241585829804002867 93807362378744706004301)
                ·
                  refine ⟨35177760892029264751613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93807362378744706004301 35177760892029264751613)
                  ·
                    refine ⟨13191660334510974281855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35177760892029264751613 13191660334510974281855)
                    ·
                      rfl

theorem cell22_38536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_38536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38536 prefixEnd_38536 := by exact prefixLift 38536
  have htrace : WordTrace (prefixWord ++ tailWord_38536) baseStart_38536 baseEnd_38536 := by
    simpa [prefixWord, tailWord_38536, baseEnd_38536] using wordTrace_append hprefix tailTrace_38536
  have hstable : (prefixWord ++ tailWord_38536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38536).length < 2 ^ (prefixWord ++ tailWord_38536).sum := by decide
  have hdescent : baseEnd_38536 < baseStart_38536 := by decide
  rcases family_descends (prefixWord ++ tailWord_38536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38545 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_38545 : Nat := 118140960795 + 38545 * 2 ^ 59
def prefixEnd_38545 : Nat := 4983230072969 + 3 ^ 40 * 38545 * 2
def baseEnd_38545 : Nat := 13194741218437950806827

theorem tailTrace_38545 : CollatzResearch.WordTrace tailWord_38545 prefixEnd_38545 13194741218437950806827 := by
  unfold tailWord_38545
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405851645365522807013089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 937234430243681871342059 1405851645365522807013089)
  ·
    refine ⟨1054388734024142105259817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1405851645365522807013089 1054388734024142105259817)
    ·
      refine ⟨790791550518106578944863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1054388734024142105259817 790791550518106578944863)
      ·
        refine ⟨1186187325777159868417295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790791550518106578944863 1186187325777159868417295)
        ·
          refine ⟨1779280988665739802625943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186187325777159868417295 1779280988665739802625943)
          ·
            refine ⟨2668921482998609703938915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779280988665739802625943 2668921482998609703938915)
            ·
              refine ⟨4003382224497914555908373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668921482998609703938915 4003382224497914555908373)
              ·
                refine ⟨187658541773339744808205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4003382224497914555908373 187658541773339744808205)
                ·
                  refine ⟨70371953165002404303077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187658541773339744808205 70371953165002404303077)
                  ·
                    refine ⟨13194741218437950806827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70371953165002404303077 13194741218437950806827)
                    ·
                      rfl

theorem cell22_38545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_38545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38545 prefixEnd_38545 := by exact prefixLift 38545
  have htrace : WordTrace (prefixWord ++ tailWord_38545) baseStart_38545 baseEnd_38545 := by
    simpa [prefixWord, tailWord_38545, baseEnd_38545] using wordTrace_append hprefix tailTrace_38545
  have hstable : (prefixWord ++ tailWord_38545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38545).length < 2 ^ (prefixWord ++ tailWord_38545).sum := by decide
  have hdescent : baseEnd_38545 < baseStart_38545 := by decide
  rcases family_descends (prefixWord ++ tailWord_38545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38575 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_38575 : Nat := 118140960795 + 38575 * 2 ^ 59
def prefixEnd_38575 : Nat := 4983230072969 + 3 ^ 40 * 38575 * 2
def baseEnd_38575 : Nat := 13205010831527872556735

theorem tailTrace_38575 : CollatzResearch.WordTrace tailWord_38575 prefixEnd_38575 13205010831527872556735 := by
  unfold tailWord_38575
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406945835256837930605179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 937963890171225287070119 1406945835256837930605179)
  ·
    refine ⟨2110418752885256895907769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1406945835256837930605179 2110418752885256895907769)
    ·
      refine ⟨1582814064663942671930827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2110418752885256895907769 1582814064663942671930827)
      ·
        refine ⟨2374221096995914007896241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582814064663942671930827 2374221096995914007896241)
        ·
          refine ⟨1780665822746935505922181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2374221096995914007896241 1780665822746935505922181)
          ·
            refine ⟨333874841765050407360409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1780665822746935505922181 333874841765050407360409)
            ·
              refine ⟨250406131323787805520307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333874841765050407360409 250406131323787805520307)
              ·
                refine ⟨375609196985681708280461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250406131323787805520307 375609196985681708280461)
                ·
                  refine ⟨140853448869630640605173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375609196985681708280461 140853448869630640605173)
                  ·
                    refine ⟨13205010831527872556735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 140853448869630640605173 13205010831527872556735)
                    ·
                      rfl

theorem cell22_38575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_38575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38575 prefixEnd_38575 := by exact prefixLift 38575
  have htrace : WordTrace (prefixWord ++ tailWord_38575) baseStart_38575 baseEnd_38575 := by
    simpa [prefixWord, tailWord_38575, baseEnd_38575] using wordTrace_append hprefix tailTrace_38575
  have hstable : (prefixWord ++ tailWord_38575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38575).length < 2 ^ (prefixWord ++ tailWord_38575).sum := by decide
  have hdescent : baseEnd_38575 < baseStart_38575 := by decide
  rcases family_descends (prefixWord ++ tailWord_38575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38592 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_38592 : Nat := 118140960795 + 38592 * 2 ^ 59
def prefixEnd_38592 : Nat := 4983230072969 + 3 ^ 40 * 38592 * 2
def baseEnd_38592 : Nat := 13210830278945494881683

theorem tailTrace_38592 : CollatzResearch.WordTrace tailWord_38592 prefixEnd_38592 13210830278945494881683 := by
  unfold tailWord_38592
  simp only [CollatzResearch.WordTrace]
  refine ⟨703782938097624916987015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 938377250796833222649353 703782938097624916987015)
  ·
    refine ⟨1055674407146437375480523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703782938097624916987015 1055674407146437375480523)
    ·
      refine ⟨1583511610719656063220785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055674407146437375480523 1583511610719656063220785)
      ·
        refine ⟨1187633708039742047415589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583511610719656063220785 1187633708039742047415589)
        ·
          refine ⟨222681320257451633890423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1187633708039742047415589 222681320257451633890423)
          ·
            refine ⟨334021980386177450835635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222681320257451633890423 334021980386177450835635)
            ·
              refine ⟨501032970579266176253453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334021980386177450835635 501032970579266176253453)
              ·
                refine ⟨187887363967224816095045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501032970579266176253453 187887363967224816095045)
                ·
                  refine ⟨35228880743854653017821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187887363967224816095045 35228880743854653017821)
                  ·
                    refine ⟨13210830278945494881683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35228880743854653017821 13210830278945494881683)
                    ·
                      rfl

theorem cell22_38592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_38592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38592 prefixEnd_38592 := by exact prefixLift 38592
  have htrace : WordTrace (prefixWord ++ tailWord_38592) baseStart_38592 baseEnd_38592 := by
    simpa [prefixWord, tailWord_38592, baseEnd_38592] using wordTrace_append hprefix tailTrace_38592
  have hstable : (prefixWord ++ tailWord_38592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38592).length < 2 ^ (prefixWord ++ tailWord_38592).sum := by decide
  have hdescent : baseEnd_38592 < baseStart_38592 := by decide
  rcases family_descends (prefixWord ++ tailWord_38592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38609 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_38609 : Nat := 118140960795 + 38609 * 2 ^ 59
def prefixEnd_38609 : Nat := 4983230072969 + 3 ^ 40 * 38609 * 2
def baseEnd_38609 : Nat := 13216649726363117206631

theorem tailTrace_38609 : CollatzResearch.WordTrace tailWord_38609 prefixEnd_38609 13216649726363117206631 := by
  unfold tailWord_38609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408185917133661737342881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 938790611422441158228587 1408185917133661737342881)
  ·
    refine ⟨1056139437850246303007161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1408185917133661737342881 1056139437850246303007161)
    ·
      refine ⟨792104578387684727255371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1056139437850246303007161 792104578387684727255371)
      ·
        refine ⟨1188156867581527090883057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792104578387684727255371 1188156867581527090883057)
        ·
          refine ⟨891117650686145318162293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188156867581527090883057 891117650686145318162293)
          ·
            refine ⟨83542279751826123577715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 891117650686145318162293 83542279751826123577715)
            ·
              refine ⟨125313419627739185366573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83542279751826123577715 125313419627739185366573)
              ·
                refine ⟨46992532360402194512465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125313419627739185366573 46992532360402194512465)
                ·
                  refine ⟨35244399270301645884349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46992532360402194512465 35244399270301645884349)
                  ·
                    refine ⟨13216649726363117206631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35244399270301645884349 13216649726363117206631)
                    ·
                      rfl

theorem cell22_38609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_38609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38609 prefixEnd_38609 := by exact prefixLift 38609
  have htrace : WordTrace (prefixWord ++ tailWord_38609) baseStart_38609 baseEnd_38609 := by
    simpa [prefixWord, tailWord_38609, baseEnd_38609] using wordTrace_append hprefix tailTrace_38609
  have hstable : (prefixWord ++ tailWord_38609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38609).length < 2 ^ (prefixWord ++ tailWord_38609).sum := by decide
  have hdescent : baseEnd_38609 < baseStart_38609 := by decide
  rcases family_descends (prefixWord ++ tailWord_38609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38667 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 5]
def baseStart_38667 : Nat := 118140960795 + 38667 * 2 ^ 59
def prefixEnd_38667 : Nat := 4983230072969 + 3 ^ 40 * 38667 * 2
def baseEnd_38667 : Nat := 4412168103890099752151

theorem tailTrace_38667 : CollatzResearch.WordTrace tailWord_38667 prefixEnd_38667 4412168103890099752151 := by
  unfold tailWord_38667
  simp only [CollatzResearch.WordTrace]
  refine ⟨1410301350923537642954255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 940200900615691761969503 1410301350923537642954255)
  ·
    refine ⟨2115452026385306464431383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1410301350923537642954255 2115452026385306464431383)
    ·
      refine ⟨3173178039577959696647075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115452026385306464431383 3173178039577959696647075)
      ·
        refine ⟨4759767059366939544970613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173178039577959696647075 4759767059366939544970613)
        ·
          refine ⟨446228161815650582340995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4759767059366939544970613 446228161815650582340995)
          ·
            refine ⟨669342242723475873511493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446228161815650582340995 669342242723475873511493)
            ·
              refine ⟨125501670510651726283405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 669342242723475873511493 125501670510651726283405)
              ·
                refine ⟨47063126441494397356277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125501670510651726283405 47063126441494397356277)
                ·
                  refine ⟨4412168103890099752151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47063126441494397356277 4412168103890099752151)
                  ·
                    rfl

theorem cell22_38667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 5].length) (baseStart_38667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38667 prefixEnd_38667 := by exact prefixLift 38667
  have htrace : WordTrace (prefixWord ++ tailWord_38667) baseStart_38667 baseEnd_38667 := by
    simpa [prefixWord, tailWord_38667, baseEnd_38667] using wordTrace_append hprefix tailTrace_38667
  have hstable : (prefixWord ++ tailWord_38667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38667).length < 2 ^ (prefixWord ++ tailWord_38667).sum := by decide
  have hdescent : baseEnd_38667 < baseStart_38667 := by decide
  rcases family_descends (prefixWord ++ tailWord_38667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38712 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_38712 : Nat := 118140960795 + 38712 * 2 ^ 59
def prefixEnd_38712 : Nat := 4983230072969 + 3 ^ 40 * 38712 * 2
def baseEnd_38712 : Nat := 4417302910435060627105

theorem tailTrace_38712 : CollatzResearch.WordTrace tailWord_38712 prefixEnd_38712 4417302910435060627105 := by
  unfold tailWord_38712
  simp only [CollatzResearch.WordTrace]
  refine ⟨705971317880255164171195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 941295090507006885561593 705971317880255164171195)
  ·
    refine ⟨1058956976820382746256793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705971317880255164171195 1058956976820382746256793)
    ·
      refine ⟨794217732615287059692595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1058956976820382746256793 794217732615287059692595)
      ·
        refine ⟨1191326598922930589538893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794217732615287059692595 1191326598922930589538893)
        ·
          refine ⟨446747474596098971077085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1191326598922930589538893 446747474596098971077085)
          ·
            refine ⟨167530302973537114153907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446747474596098971077085 167530302973537114153907)
            ·
              refine ⟨251295454460305671230861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167530302973537114153907 251295454460305671230861)
              ·
                refine ⟨94235795422614626711573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251295454460305671230861 94235795422614626711573)
                ·
                  refine ⟨4417302910435060627105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94235795422614626711573 4417302910435060627105)
                  ·
                    rfl

theorem cell22_38712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_38712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38712 prefixEnd_38712 := by exact prefixLift 38712
  have htrace : WordTrace (prefixWord ++ tailWord_38712) baseStart_38712 baseEnd_38712 := by
    simpa [prefixWord, tailWord_38712, baseEnd_38712] using wordTrace_append hprefix tailTrace_38712
  have hstable : (prefixWord ++ tailWord_38712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38712).length < 2 ^ (prefixWord ++ tailWord_38712).sum := by decide
  have hdescent : baseEnd_38712 < baseStart_38712 := by decide
  rcases family_descends (prefixWord ++ tailWord_38712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38759 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_38759 : Nat := 118140960795 + 38759 * 2 ^ 59
def prefixEnd_38759 : Nat := 4983230072969 + 3 ^ 40 * 38759 * 2
def baseEnd_38759 : Nat := 13267997791812725956171

theorem tailTrace_38759 : CollatzResearch.WordTrace tailWord_38759 prefixEnd_38759 13267997791812725956171 := by
  unfold tailWord_38759
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413656866590237355303331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 942437911060158236868887 1413656866590237355303331)
  ·
    refine ⟨2120485299885356032954997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413656866590237355303331 2120485299885356032954997)
    ·
      refine ⟨198795496864252128089531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2120485299885356032954997 198795496864252128089531)
      ·
        refine ⟨298193245296378192134297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198795496864252128089531 298193245296378192134297)
        ·
          refine ⟨223644933972283644100723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298193245296378192134297 223644933972283644100723)
          ·
            refine ⟨335467400958425466151085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223644933972283644100723 335467400958425466151085)
            ·
              refine ⟨125800275359409549806657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335467400958425466151085 125800275359409549806657)
              ·
                refine ⟨94350206519557162354993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125800275359409549806657 94350206519557162354993)
                ·
                  refine ⟨70762654889667871766245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94350206519557162354993 70762654889667871766245)
                  ·
                    refine ⟨13267997791812725956171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70762654889667871766245 13267997791812725956171)
                    ·
                      rfl

theorem cell22_38759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_38759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38759 prefixEnd_38759 := by exact prefixLift 38759
  have htrace : WordTrace (prefixWord ++ tailWord_38759) baseStart_38759 baseEnd_38759 := by
    simpa [prefixWord, tailWord_38759, baseEnd_38759] using wordTrace_append hprefix tailTrace_38759
  have hstable : (prefixWord ++ tailWord_38759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38759).length < 2 ^ (prefixWord ++ tailWord_38759).sum := by decide
  have hdescent : baseEnd_38759 < baseStart_38759 := by decide
  rcases family_descends (prefixWord ++ tailWord_38759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38789 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_38789 : Nat := 118140960795 + 38789 * 2 ^ 59
def prefixEnd_38789 : Nat := 4983230072969 + 3 ^ 40 * 38789 * 2
def baseEnd_38789 : Nat := 13278267404902647706079

theorem tailTrace_38789 : CollatzResearch.WordTrace tailWord_38789 prefixEnd_38789 13278267404902647706079 := by
  unfold tailWord_38789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414751056481552478895421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 943167370987701652596947 1414751056481552478895421)
  ·
    refine ⟨530531646180582179585783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1414751056481552478895421 530531646180582179585783)
    ·
      refine ⟨795797469270873269378675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530531646180582179585783 795797469270873269378675)
      ·
        refine ⟨1193696203906309904068013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795797469270873269378675 1193696203906309904068013)
        ·
          refine ⟨447636076464866214025505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1193696203906309904068013 447636076464866214025505)
          ·
            refine ⟨335727057348649660519129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447636076464866214025505 335727057348649660519129)
            ·
              refine ⟨251795293011487245389347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335727057348649660519129 251795293011487245389347)
              ·
                refine ⟨377692939517230868084021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251795293011487245389347 377692939517230868084021)
                ·
                  refine ⟨35408713079740393882877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377692939517230868084021 35408713079740393882877)
                  ·
                    refine ⟨13278267404902647706079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35408713079740393882877 13278267404902647706079)
                    ·
                      rfl

theorem cell22_38789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_38789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38789 prefixEnd_38789 := by exact prefixLift 38789
  have htrace : WordTrace (prefixWord ++ tailWord_38789) baseStart_38789 baseEnd_38789 := by
    simpa [prefixWord, tailWord_38789, baseEnd_38789] using wordTrace_append hprefix tailTrace_38789
  have hstable : (prefixWord ++ tailWord_38789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38789).length < 2 ^ (prefixWord ++ tailWord_38789).sum := by decide
  have hdescent : baseEnd_38789 < baseStart_38789 := by decide
  rcases family_descends (prefixWord ++ tailWord_38789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38814 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_38814 : Nat := 118140960795 + 38814 * 2 ^ 59
def prefixEnd_38814 : Nat := 4983230072969 + 3 ^ 40 * 38814 * 2
def baseEnd_38814 : Nat := 4428941805270305277001

theorem tailTrace_38814 : CollatzResearch.WordTrace tailWord_38814 prefixEnd_38814 4428941805270305277001 := by
  unfold tailWord_38814
  simp only [CollatzResearch.WordTrace]
  refine ⟨176957860173872718569437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 943775254260654499036997 176957860173872718569437)
  ·
    refine ⟨66359197565202269463539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176957860173872718569437 66359197565202269463539)
    ·
      refine ⟨99538796347803404195309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66359197565202269463539 99538796347803404195309)
      ·
        refine ⟨37327048630426276573241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99538796347803404195309 37327048630426276573241)
        ·
          refine ⟨27995286472819707429931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37327048630426276573241 27995286472819707429931)
          ·
            refine ⟨41992929709229561144897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27995286472819707429931 41992929709229561144897)
            ·
              refine ⟨31494697281922170858673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41992929709229561144897 31494697281922170858673)
              ·
                refine ⟨23621022961441628144005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31494697281922170858673 23621022961441628144005)
                ·
                  refine ⟨4428941805270305277001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23621022961441628144005 4428941805270305277001)
                  ·
                    rfl

theorem cell22_38814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_38814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38814 prefixEnd_38814 := by exact prefixLift 38814
  have htrace : WordTrace (prefixWord ++ tailWord_38814) baseStart_38814 baseEnd_38814 := by
    simpa [prefixWord, tailWord_38814, baseEnd_38814] using wordTrace_append hprefix tailTrace_38814
  have hstable : (prefixWord ++ tailWord_38814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38814).length < 2 ^ (prefixWord ++ tailWord_38814).sum := by decide
  have hdescent : baseEnd_38814 < baseStart_38814 := by decide
  rcases family_descends (prefixWord ++ tailWord_38814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38870 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_38870 : Nat := 118140960795 + 38870 * 2 ^ 59
def prefixEnd_38870 : Nat := 4983230072969 + 3 ^ 40 * 38870 * 2
def baseEnd_38870 : Nat := 4435331786748478810277

theorem tailTrace_38870 : CollatzResearch.WordTrace tailWord_38870 prefixEnd_38870 4435331786748478810277 := by
  unfold tailWord_38870
  simp only [CollatzResearch.WordTrace]
  refine ⟨88606585574256457037129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 945136912792068875062709 88606585574256457037129)
  ·
    refine ⟨66454939180692342777847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88606585574256457037129 66454939180692342777847)
    ·
      refine ⟨99682408771038514166771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66454939180692342777847 99682408771038514166771)
      ·
        refine ⟨149523613156557771250157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99682408771038514166771 149523613156557771250157)
        ·
          refine ⟨56071354933709164218809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149523613156557771250157 56071354933709164218809)
          ·
            refine ⟨42053516200281873164107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56071354933709164218809 42053516200281873164107)
            ·
              refine ⟨63080274300422809746161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42053516200281873164107 63080274300422809746161)
              ·
                refine ⟨47310205725317107309621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63080274300422809746161 47310205725317107309621)
                ·
                  refine ⟨4435331786748478810277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47310205725317107309621 4435331786748478810277)
                  ·
                    rfl

theorem cell22_38870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_38870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38870 prefixEnd_38870 := by exact prefixLift 38870
  have htrace : WordTrace (prefixWord ++ tailWord_38870) baseStart_38870 baseEnd_38870 := by
    simpa [prefixWord, tailWord_38870, baseEnd_38870] using wordTrace_append hprefix tailTrace_38870
  have hstable : (prefixWord ++ tailWord_38870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38870).length < 2 ^ (prefixWord ++ tailWord_38870).sum := by decide
  have hdescent : baseEnd_38870 < baseStart_38870 := by decide
  rcases family_descends (prefixWord ++ tailWord_38870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38881 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 4]
def baseStart_38881 : Nat := 118140960795 + 38881 * 2 ^ 59
def prefixEnd_38881 : Nat := 4983230072969 + 3 ^ 40 * 38881 * 2
def baseEnd_38881 : Nat := 4436586961681691468599

theorem tailTrace_38881 : CollatzResearch.WordTrace tailWord_38881 prefixEnd_38881 4436586961681691468599 := by
  unfold tailWord_38881
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418106572148252191244497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 945404381432168127496331 1418106572148252191244497)
  ·
    refine ⟨1063579929111189143433373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1418106572148252191244497 1063579929111189143433373)
    ·
      refine ⟨398842473416695928787515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1063579929111189143433373 398842473416695928787515)
      ·
        refine ⟨598263710125043893181273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398842473416695928787515 598263710125043893181273)
        ·
          refine ⟨448697782593782919885955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598263710125043893181273 448697782593782919885955)
          ·
            refine ⟨673046673890674379828933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448697782593782919885955 673046673890674379828933)
            ·
              refine ⟨126196251354501446217925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 673046673890674379828933 126196251354501446217925)
              ·
                refine ⟨23661797128969021165861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126196251354501446217925 23661797128969021165861)
                ·
                  refine ⟨4436586961681691468599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23661797128969021165861 4436586961681691468599)
                  ·
                    rfl

theorem cell22_38881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_38881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38881 prefixEnd_38881 := by exact prefixLift 38881
  have htrace : WordTrace (prefixWord ++ tailWord_38881) baseStart_38881 baseEnd_38881 := by
    simpa [prefixWord, tailWord_38881, baseEnd_38881] using wordTrace_append hprefix tailTrace_38881
  have hstable : (prefixWord ++ tailWord_38881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38881).length < 2 ^ (prefixWord ++ tailWord_38881).sum := by decide
  have hdescent : baseEnd_38881 < baseStart_38881 := by decide
  rcases family_descends (prefixWord ++ tailWord_38881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38896 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_38896 : Nat := 118140960795 + 38896 * 2 ^ 59
def prefixEnd_38896 : Nat := 4983230072969 + 3 ^ 40 * 38896 * 2
def baseEnd_38896 : Nat := 13314895691590035280751

theorem tailTrace_38896 : CollatzResearch.WordTrace tailWord_38896 prefixEnd_38896 13314895691590035280751 := by
  unfold tailWord_38896
  simp only [CollatzResearch.WordTrace]
  refine ⟨709326833546954876520271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 945769111395939835360361 709326833546954876520271)
  ·
    refine ⟨1063990250320432314780407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709326833546954876520271 1063990250320432314780407)
    ·
      refine ⟨1595985375480648472170611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063990250320432314780407 1595985375480648472170611)
      ·
        refine ⟨2393978063220972708255917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595985375480648472170611 2393978063220972708255917)
        ·
          refine ⟨897741773707864765595969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2393978063220972708255917 897741773707864765595969)
          ·
            refine ⟨673306330280898574196977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897741773707864765595969 673306330280898574196977)
            ·
              refine ⟨504979747710673930647733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673306330280898574196977 504979747710673930647733)
              ·
                refine ⟨47341851347875680998225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 504979747710673930647733 47341851347875680998225)
                ·
                  refine ⟨35506388510906760748669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47341851347875680998225 35506388510906760748669)
                  ·
                    refine ⟨13314895691590035280751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35506388510906760748669 13314895691590035280751)
                    ·
                      rfl

theorem cell22_38896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_38896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38896 prefixEnd_38896 := by exact prefixLift 38896
  have htrace : WordTrace (prefixWord ++ tailWord_38896) baseStart_38896 baseEnd_38896 := by
    simpa [prefixWord, tailWord_38896, baseEnd_38896] using wordTrace_append hprefix tailTrace_38896
  have hstable : (prefixWord ++ tailWord_38896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38896).length < 2 ^ (prefixWord ++ tailWord_38896).sum := by decide
  have hdescent : baseEnd_38896 < baseStart_38896 := by decide
  rcases family_descends (prefixWord ++ tailWord_38896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38932 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_38932 : Nat := 118140960795 + 38932 * 2 ^ 59
def prefixEnd_38932 : Nat := 4983230072969 + 3 ^ 40 * 38932 * 2
def baseEnd_38932 : Nat := 4442406409099313793547

theorem tailTrace_38932 : CollatzResearch.WordTrace tailWord_38932 prefixEnd_38932 4442406409099313793547 := by
  unfold tailWord_38932
  simp only [CollatzResearch.WordTrace]
  refine ⟨709983347481743950675525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 946644463308991934234033 709983347481743950675525)
  ·
    refine ⟨133121877652826990751661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 709983347481743950675525 133121877652826990751661)
    ·
      refine ⟨49920704119810121531873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133121877652826990751661 49920704119810121531873)
      ·
        refine ⟨37440528089857591148905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49920704119810121531873 37440528089857591148905)
        ·
          refine ⟨28080396067393193361679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37440528089857591148905 28080396067393193361679)
          ·
            refine ⟨42120594101089790042519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28080396067393193361679 42120594101089790042519)
            ·
              refine ⟨63180891151634685063779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42120594101089790042519 63180891151634685063779)
              ·
                refine ⟨94771336727452027595669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63180891151634685063779 94771336727452027595669)
                ·
                  refine ⟨4442406409099313793547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94771336727452027595669 4442406409099313793547)
                  ·
                    rfl

theorem cell22_38932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_38932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_38932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_38932 prefixEnd_38932 := by exact prefixLift 38932
  have htrace : WordTrace (prefixWord ++ tailWord_38932) baseStart_38932 baseEnd_38932 := by
    simpa [prefixWord, tailWord_38932, baseEnd_38932] using wordTrace_append hprefix tailTrace_38932
  have hstable : (prefixWord ++ tailWord_38932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38932).length < 2 ^ (prefixWord ++ tailWord_38932).sum := by decide
  have hdescent : baseEnd_38932 < baseStart_38932 := by decide
  rcases family_descends (prefixWord ++ tailWord_38932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39031 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_39031 : Nat := 118140960795 + 39031 * 2 ^ 59
def prefixEnd_39031 : Nat := 4983230072969 + 3 ^ 40 * 39031 * 2
def baseEnd_39031 : Nat := 13361108950494683155337

theorem tailTrace_39031 : CollatzResearch.WordTrace tailWord_39031 prefixEnd_39031 13361108950494683155337 := by
  unfold tailWord_39031
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423577521604827809204947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949051681069885206136631 1423577521604827809204947)
  ·
    refine ⟨2135366282407241713807421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1423577521604827809204947 2135366282407241713807421)
    ·
      refine ⟨800762355902715642677783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2135366282407241713807421 800762355902715642677783)
      ·
        refine ⟨1201143533854073464016675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800762355902715642677783 1201143533854073464016675)
        ·
          refine ⟨1801715300781110196025013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201143533854073464016675 1801715300781110196025013)
          ·
            refine ⟨168910809448229080877345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1801715300781110196025013 168910809448229080877345)
            ·
              refine ⟨126683107086171810658009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168910809448229080877345 126683107086171810658009)
              ·
                refine ⟨95012330314628857993507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126683107086171810658009 95012330314628857993507)
                ·
                  refine ⟨142518495471943286990261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95012330314628857993507 142518495471943286990261)
                  ·
                    refine ⟨13361108950494683155337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142518495471943286990261 13361108950494683155337)
                    ·
                      rfl

theorem cell22_39031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_39031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39031 prefixEnd_39031 := by exact prefixLift 39031
  have htrace : WordTrace (prefixWord ++ tailWord_39031) baseStart_39031 baseEnd_39031 := by
    simpa [prefixWord, tailWord_39031, baseEnd_39031] using wordTrace_append hprefix tailTrace_39031
  have hstable : (prefixWord ++ tailWord_39031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39031).length < 2 ^ (prefixWord ++ tailWord_39031).sum := by decide
  have hdescent : baseEnd_39031 < baseStart_39031 := by decide
  rcases family_descends (prefixWord ++ tailWord_39031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39033 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 4]
def baseStart_39033 : Nat := 118140960795 + 39033 * 2 ^ 59
def prefixEnd_39033 : Nat := 4983230072969 + 3 ^ 40 * 39033 * 2
def baseEnd_39033 : Nat := 4453931197122448201777

theorem tailTrace_39033 : CollatzResearch.WordTrace tailWord_39033 prefixEnd_39033 4453931197122448201777 := by
  unfold tailWord_39033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423650467597582150777753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949100311731721433851835 1423650467597582150777753)
  ·
    refine ⟨1067737850698186613083315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423650467597582150777753 1067737850698186613083315)
    ·
      refine ⟨1601606776047279919624973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067737850698186613083315 1601606776047279919624973)
      ·
        refine ⟨600602541017729969859365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1601606776047279919624973 600602541017729969859365)
        ·
          refine ⟨112612976440824369348631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 600602541017729969859365 112612976440824369348631)
          ·
            refine ⟨168919464661236554022947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112612976440824369348631 168919464661236554022947)
            ·
              refine ⟨253379196991854831034421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168919464661236554022947 253379196991854831034421)
              ·
                refine ⟨23754299717986390409477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253379196991854831034421 23754299717986390409477)
                ·
                  refine ⟨4453931197122448201777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23754299717986390409477 4453931197122448201777)
                  ·
                    rfl

theorem cell22_39033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_39033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39033 prefixEnd_39033 := by exact prefixLift 39033
  have htrace : WordTrace (prefixWord ++ tailWord_39033) baseStart_39033 baseEnd_39033 := by
    simpa [prefixWord, tailWord_39033, baseEnd_39033] using wordTrace_append hprefix tailTrace_39033
  have hstable : (prefixWord ++ tailWord_39033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39033).length < 2 ^ (prefixWord ++ tailWord_39033).sum := by decide
  have hdescent : baseEnd_39033 < baseStart_39033 := by decide
  rcases family_descends (prefixWord ++ tailWord_39033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39116 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_39116 : Nat := 118140960795 + 39116 * 2 ^ 59
def prefixEnd_39116 : Nat := 4983230072969 + 3 ^ 40 * 39116 * 2
def baseEnd_39116 : Nat := 13390206187582794780077

theorem tailTrace_39116 : CollatzResearch.WordTrace tailWord_39116 prefixEnd_39116 13390206187582794780077 := by
  unfold tailWord_39116
  simp only [CollatzResearch.WordTrace]
  refine ⟨713338863148443663024601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 951118484197924884032801 713338863148443663024601)
  ·
    refine ⟨535004147361332747268451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 713338863148443663024601 535004147361332747268451)
    ·
      refine ⟨802506221041999120902677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535004147361332747268451 802506221041999120902677)
      ·
        refine ⟨37617479111343708792313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 802506221041999120902677 37617479111343708792313)
        ·
          refine ⟨28213109333507781594235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37617479111343708792313 28213109333507781594235)
          ·
            refine ⟨42319664000261672391353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28213109333507781594235 42319664000261672391353)
            ·
              refine ⟨31739748000196254293515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42319664000261672391353 31739748000196254293515)
              ·
                refine ⟨47609622000294381440273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31739748000196254293515 47609622000294381440273)
                ·
                  refine ⟨35707216500220786080205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47609622000294381440273 35707216500220786080205)
                  ·
                    refine ⟨13390206187582794780077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35707216500220786080205 13390206187582794780077)
                    ·
                      rfl

theorem cell22_39116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_39116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39116 prefixEnd_39116 := by exact prefixLift 39116
  have htrace : WordTrace (prefixWord ++ tailWord_39116) baseStart_39116 baseEnd_39116 := by
    simpa [prefixWord, tailWord_39116, baseEnd_39116] using wordTrace_append hprefix tailTrace_39116
  have hstable : (prefixWord ++ tailWord_39116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39116).length < 2 ^ (prefixWord ++ tailWord_39116).sum := by decide
  have hdescent : baseEnd_39116 < baseStart_39116 := by decide
  rcases family_descends (prefixWord ++ tailWord_39116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39121 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_39121 : Nat := 118140960795 + 39121 * 2 ^ 59
def prefixEnd_39121 : Nat := 4983230072969 + 3 ^ 40 * 39121 * 2
def baseEnd_39121 : Nat := 13391917789764448405061

theorem tailTrace_39121 : CollatzResearch.WordTrace tailWord_39121 prefixEnd_39121 13391917789764448405061 := by
  unfold tailWord_39121
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426860091278773179981217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 951240060852515453320811 1426860091278773179981217)
  ·
    refine ⟨1070145068459079884985913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1426860091278773179981217 1070145068459079884985913)
    ·
      refine ⟨802608801344309913739435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1070145068459079884985913 802608801344309913739435)
      ·
        refine ⟨1203913202016464870609153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802608801344309913739435 1203913202016464870609153)
        ·
          refine ⟨902934901512348652956865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203913202016464870609153 902934901512348652956865)
          ·
            refine ⟨677201176134261489717649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902934901512348652956865 677201176134261489717649)
            ·
              refine ⟨507900882100696117288237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677201176134261489717649 507900882100696117288237)
              ·
                refine ⟨190462830787761043983089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507900882100696117288237 190462830787761043983089)
                ·
                  refine ⟨142847123090820782987317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190462830787761043983089 142847123090820782987317)
                  ·
                    refine ⟨13391917789764448405061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142847123090820782987317 13391917789764448405061)
                    ·
                      rfl

theorem cell22_39121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_39121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39121 prefixEnd_39121 := by exact prefixLift 39121
  have htrace : WordTrace (prefixWord ++ tailWord_39121) baseStart_39121 baseEnd_39121 := by
    simpa [prefixWord, tailWord_39121, baseEnd_39121] using wordTrace_append hprefix tailTrace_39121
  have hstable : (prefixWord ++ tailWord_39121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39121).length < 2 ^ (prefixWord ++ tailWord_39121).sum := by decide
  have hdescent : baseEnd_39121 < baseStart_39121 := by decide
  rcases family_descends (prefixWord ++ tailWord_39121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39153 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_39153 : Nat := 118140960795 + 39153 * 2 ^ 59
def prefixEnd_39153 : Nat := 4983230072969 + 3 ^ 40 * 39153 * 2
def baseEnd_39153 : Nat := 13402872043727031604963

theorem tailTrace_39153 : CollatzResearch.WordTrace tailWord_39153 prefixEnd_39153 13402872043727031604963 := by
  unfold tailWord_39153
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428027227162842645146113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 952018151441895096764075 1428027227162842645146113)
  ·
    refine ⟨1071020420372131983859585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1428027227162842645146113 1071020420372131983859585)
    ·
      refine ⟨803265315279098987894689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071020420372131983859585 803265315279098987894689)
      ·
        refine ⟨602448986459324240921017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803265315279098987894689 602448986459324240921017)
        ·
          refine ⟨451836739844493180690763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602448986459324240921017 451836739844493180690763)
          ·
            refine ⟨677755109766739771036145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451836739844493180690763 677755109766739771036145)
            ·
              refine ⟨508316332325054828277109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677755109766739771036145 508316332325054828277109)
              ·
                refine ⟨47654656155473890150979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508316332325054828277109 47654656155473890150979)
                ·
                  refine ⟨71481984233210835226469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47654656155473890150979 71481984233210835226469)
                  ·
                    refine ⟨13402872043727031604963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71481984233210835226469 13402872043727031604963)
                    ·
                      rfl

theorem cell22_39153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_39153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39153 prefixEnd_39153 := by exact prefixLift 39153
  have htrace : WordTrace (prefixWord ++ tailWord_39153) baseStart_39153 baseEnd_39153 := by
    simpa [prefixWord, tailWord_39153, baseEnd_39153] using wordTrace_append hprefix tailTrace_39153
  have hstable : (prefixWord ++ tailWord_39153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39153).length < 2 ^ (prefixWord ++ tailWord_39153).sum := by decide
  have hdescent : baseEnd_39153 < baseStart_39153 := by decide
  rcases family_descends (prefixWord ++ tailWord_39153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39170 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_39170 : Nat := 118140960795 + 39170 * 2 ^ 59
def prefixEnd_39170 : Nat := 4983230072969 + 3 ^ 40 * 39170 * 2
def baseEnd_39170 : Nat := 13408691491144653929911

theorem tailTrace_39170 : CollatzResearch.WordTrace tailWord_39170 prefixEnd_39170 13408691491144653929911 := by
  unfold tailWord_39170
  simp only [CollatzResearch.WordTrace]
  refine ⟨357161817025313637128741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 952431512067503032343309 357161817025313637128741)
  ·
    refine ⟨66967840692246306961639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 357161817025313637128741 66967840692246306961639)
    ·
      refine ⟨100451761038369460442459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66967840692246306961639 100451761038369460442459)
      ·
        refine ⟨150677641557554190663689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100451761038369460442459 150677641557554190663689)
        ·
          refine ⟨113008231168165642997767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150677641557554190663689 113008231168165642997767)
          ·
            refine ⟨169512346752248464496651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113008231168165642997767 169512346752248464496651)
            ·
              refine ⟨254268520128372696744977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169512346752248464496651 254268520128372696744977)
              ·
                refine ⟨190701390096279522558733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254268520128372696744977 190701390096279522558733)
                ·
                  refine ⟨71513021286104820959525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190701390096279522558733 71513021286104820959525)
                  ·
                    refine ⟨13408691491144653929911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71513021286104820959525 13408691491144653929911)
                    ·
                      rfl

theorem cell22_39170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_39170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39170 prefixEnd_39170 := by exact prefixLift 39170
  have htrace : WordTrace (prefixWord ++ tailWord_39170) baseStart_39170 baseEnd_39170 := by
    simpa [prefixWord, tailWord_39170, baseEnd_39170] using wordTrace_append hprefix tailTrace_39170
  have hstable : (prefixWord ++ tailWord_39170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39170).length < 2 ^ (prefixWord ++ tailWord_39170).sum := by decide
  have hdescent : baseEnd_39170 < baseStart_39170 := by decide
  rcases family_descends (prefixWord ++ tailWord_39170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39202 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_39202 : Nat := 118140960795 + 39202 * 2 ^ 59
def prefixEnd_39202 : Nat := 4983230072969 + 3 ^ 40 * 39202 * 2
def baseEnd_39202 : Nat := 4473215248369079043271

theorem tailTrace_39202 : CollatzResearch.WordTrace tailWord_39202 prefixEnd_39202 4473215248369079043271 := by
  unfold tailWord_39202
  simp only [CollatzResearch.WordTrace]
  refine ⟨357453600996331003419965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 953209602656882675786573 357453600996331003419965)
  ·
    refine ⟨134045100373624126282487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 357453600996331003419965 134045100373624126282487)
    ·
      refine ⟨201067650560436189423731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134045100373624126282487 201067650560436189423731)
      ·
        refine ⟨301601475840654284135597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201067650560436189423731 301601475840654284135597)
        ·
          refine ⟨113100553440245356550849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301601475840654284135597 113100553440245356550849)
          ·
            refine ⟨84825415080184017413137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113100553440245356550849 84825415080184017413137)
            ·
              refine ⟨63619061310138013059853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84825415080184017413137 63619061310138013059853)
              ·
                refine ⟨23857147991301754897445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63619061310138013059853 23857147991301754897445)
                ·
                  refine ⟨4473215248369079043271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23857147991301754897445 4473215248369079043271)
                  ·
                    rfl

theorem cell22_39202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_39202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39202 prefixEnd_39202 := by exact prefixLift 39202
  have htrace : WordTrace (prefixWord ++ tailWord_39202) baseStart_39202 baseEnd_39202 := by
    simpa [prefixWord, tailWord_39202, baseEnd_39202] using wordTrace_append hprefix tailTrace_39202
  have hstable : (prefixWord ++ tailWord_39202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39202).length < 2 ^ (prefixWord ++ tailWord_39202).sum := by decide
  have hdescent : baseEnd_39202 < baseStart_39202 := by decide
  rcases family_descends (prefixWord ++ tailWord_39202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39303 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 8]
def baseStart_39303 : Nat := 118140960795 + 39303 * 2 ^ 59
def prefixEnd_39303 : Nat := 4983230072969 + 3 ^ 40 * 39303 * 2
def baseEnd_39303 : Nat := 4484740036392213451501

theorem tailTrace_39303 : CollatzResearch.WordTrace tailWord_39303 prefixEnd_39303 4484740036392213451501 := by
  unfold tailWord_39303
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433498176619418263106563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 955665451079612175404375 1433498176619418263106563)
  ·
    refine ⟨2150247264929127394659845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433498176619418263106563 2150247264929127394659845)
    ·
      refine ⟨403171362174211386498721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2150247264929127394659845 403171362174211386498721)
      ·
        refine ⟨302378521630658539874041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403171362174211386498721 302378521630658539874041)
        ·
          refine ⟨226783891222993904905531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302378521630658539874041 226783891222993904905531)
          ·
            refine ⟨340175836834490857358297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226783891222993904905531 340175836834490857358297)
            ·
              refine ⟨255131877625868143018723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340175836834490857358297 255131877625868143018723)
              ·
                refine ⟨382697816438802214528085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255131877625868143018723 382697816438802214528085)
                ·
                  refine ⟨4484740036392213451501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 382697816438802214528085 4484740036392213451501)
                  ·
                    rfl

theorem cell22_39303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 8].length) (baseStart_39303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39303 prefixEnd_39303 := by exact prefixLift 39303
  have htrace : WordTrace (prefixWord ++ tailWord_39303) baseStart_39303 baseEnd_39303 := by
    simpa [prefixWord, tailWord_39303, baseEnd_39303] using wordTrace_append hprefix tailTrace_39303
  have hstable : (prefixWord ++ tailWord_39303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39303).length < 2 ^ (prefixWord ++ tailWord_39303).sum := by decide
  have hdescent : baseEnd_39303 < baseStart_39303 := by decide
  rcases family_descends (prefixWord ++ tailWord_39303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39305 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_39305 : Nat := 118140960795 + 39305 * 2 ^ 59
def prefixEnd_39305 : Nat := 4983230072969 + 3 ^ 40 * 39305 * 2
def baseEnd_39305 : Nat := 13454904750049301804497

theorem tailTrace_39305 : CollatzResearch.WordTrace tailWord_39305 prefixEnd_39305 13454904750049301804497 := by
  unfold tailWord_39305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433571122612172604679369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 955714081741448403119579 1433571122612172604679369)
  ·
    refine ⟨1075178341959129453509527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1433571122612172604679369 1075178341959129453509527)
    ·
      refine ⟨1612767512938694180264291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075178341959129453509527 1612767512938694180264291)
      ·
        refine ⟨2419151269408041270396437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612767512938694180264291 2419151269408041270396437)
        ·
          refine ⟨113397715753501934549833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2419151269408041270396437 113397715753501934549833)
          ·
            refine ⟨85048286815126450912375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113397715753501934549833 85048286815126450912375)
            ·
              refine ⟨127572430222689676368563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85048286815126450912375 127572430222689676368563)
              ·
                refine ⟨191358645334034514552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127572430222689676368563 191358645334034514552845)
                ·
                  refine ⟨71759492000262942957317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191358645334034514552845 71759492000262942957317)
                  ·
                    refine ⟨13454904750049301804497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71759492000262942957317 13454904750049301804497)
                    ·
                      rfl

theorem cell22_39305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_39305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39305 prefixEnd_39305 := by exact prefixLift 39305
  have htrace : WordTrace (prefixWord ++ tailWord_39305) baseStart_39305 baseEnd_39305 := by
    simpa [prefixWord, tailWord_39305, baseEnd_39305] using wordTrace_append hprefix tailTrace_39305
  have hstable : (prefixWord ++ tailWord_39305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39305).length < 2 ^ (prefixWord ++ tailWord_39305).sum := by decide
  have hdescent : baseEnd_39305 < baseStart_39305 := by decide
  rcases family_descends (prefixWord ++ tailWord_39305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39367 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 2, 4]
def baseStart_39367 : Nat := 118140960795 + 39367 * 2 ^ 59
def prefixEnd_39367 : Nat := 4983230072969 + 3 ^ 40 * 39367 * 2
def baseEnd_39367 : Nat := 13476128617101806754307

theorem tailTrace_39367 : CollatzResearch.WordTrace tailWord_39367 prefixEnd_39367 13476128617101806754307 := by
  unfold tailWord_39367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435832448387557193436355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 957221632258371462290903 1435832448387557193436355)
  ·
    refine ⟨2153748672581335790154533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435832448387557193436355 2153748672581335790154533)
    ·
      refine ⟨403827876109000460653975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2153748672581335790154533 403827876109000460653975)
      ·
        refine ⟨605741814163500690980963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403827876109000460653975 605741814163500690980963)
        ·
          refine ⟨908612721245251036471445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605741814163500690980963 908612721245251036471445)
          ·
            refine ⟨42591221308371142334599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 908612721245251036471445 42591221308371142334599)
            ·
              refine ⟨63886831962556713501899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42591221308371142334599 63886831962556713501899)
              ·
                refine ⟨95830247943835070252849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63886831962556713501899 95830247943835070252849)
                ·
                  refine ⟨71872685957876302689637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95830247943835070252849 71872685957876302689637)
                  ·
                    refine ⟨13476128617101806754307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71872685957876302689637 13476128617101806754307)
                    ·
                      rfl

theorem cell22_39367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_39367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39367 prefixEnd_39367 := by exact prefixLift 39367
  have htrace : WordTrace (prefixWord ++ tailWord_39367) baseStart_39367 baseEnd_39367 := by
    simpa [prefixWord, tailWord_39367, baseEnd_39367] using wordTrace_append hprefix tailTrace_39367
  have hstable : (prefixWord ++ tailWord_39367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39367).length < 2 ^ (prefixWord ++ tailWord_39367).sum := by decide
  have hdescent : baseEnd_39367 < baseStart_39367 := by decide
  rcases family_descends (prefixWord ++ tailWord_39367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39502 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_39502 : Nat := 118140960795 + 39502 * 2 ^ 59
def prefixEnd_39502 : Nat := 4983230072969 + 3 ^ 40 * 39502 * 2
def baseEnd_39502 : Nat := 13522341876006454628893

theorem tailTrace_39502 : CollatzResearch.WordTrace tailWord_39502 prefixEnd_39502 13522341876006454628893 := by
  unfold tailWord_39502
  simp only [CollatzResearch.WordTrace]
  refine ⟨180094537862309406200095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 960504201932316833067173 180094537862309406200095)
  ·
    refine ⟨270141806793464109300143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180094537862309406200095 270141806793464109300143)
    ·
      refine ⟨405212710190196163950215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270141806793464109300143 405212710190196163950215)
      ·
        refine ⟨607819065285294245925323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405212710190196163950215 607819065285294245925323)
        ·
          refine ⟨911728597927941368887985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607819065285294245925323 911728597927941368887985)
          ·
            refine ⟨683796448445956026665989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911728597927941368887985 683796448445956026665989)
            ·
              refine ⟨128211834083616754999873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 683796448445956026665989 128211834083616754999873)
              ·
                refine ⟨96158875562712566249905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128211834083616754999873 96158875562712566249905)
                ·
                  refine ⟨72119156672034424687429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96158875562712566249905 72119156672034424687429)
                  ·
                    refine ⟨13522341876006454628893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72119156672034424687429 13522341876006454628893)
                    ·
                      rfl

theorem cell22_39502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_39502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39502 prefixEnd_39502 := by exact prefixLift 39502
  have htrace : WordTrace (prefixWord ++ tailWord_39502) baseStart_39502 baseEnd_39502 := by
    simpa [prefixWord, tailWord_39502, baseEnd_39502] using wordTrace_append hprefix tailTrace_39502
  have hstable : (prefixWord ++ tailWord_39502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39502).length < 2 ^ (prefixWord ++ tailWord_39502).sum := by decide
  have hdescent : baseEnd_39502 < baseStart_39502 := by decide
  rcases family_descends (prefixWord ++ tailWord_39502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39532 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_39532 : Nat := 118140960795 + 39532 * 2 ^ 59
def prefixEnd_39532 : Nat := 4983230072969 + 3 ^ 40 * 39532 * 2
def baseEnd_39532 : Nat := 13532611489096376378801

theorem tailTrace_39532 : CollatzResearch.WordTrace tailWord_39532 prefixEnd_39532 13532611489096376378801 := by
  unfold tailWord_39532
  simp only [CollatzResearch.WordTrace]
  refine ⟨720925246394895186596425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 961233661859860248795233 720925246394895186596425)
  ·
    refine ⟨540693934796171389947319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 720925246394895186596425 540693934796171389947319)
    ·
      refine ⟨811040902194257084920979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540693934796171389947319 811040902194257084920979)
      ·
        refine ⟨1216561353291385627381469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811040902194257084920979 1216561353291385627381469)
        ·
          refine ⟨456210507484269610268051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1216561353291385627381469 456210507484269610268051)
          ·
            refine ⟨684315761226404415402077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456210507484269610268051 684315761226404415402077)
            ·
              refine ⟨256618410459901655775779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 684315761226404415402077 256618410459901655775779)
              ·
                refine ⟨384927615689852483663669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256618410459901655775779 384927615689852483663669)
                ·
                  refine ⟨36086963970923670343469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384927615689852483663669 36086963970923670343469)
                  ·
                    refine ⟨13532611489096376378801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36086963970923670343469 13532611489096376378801)
                    ·
                      rfl

theorem cell22_39532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_39532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39532 prefixEnd_39532 := by exact prefixLift 39532
  have htrace : WordTrace (prefixWord ++ tailWord_39532) baseStart_39532 baseEnd_39532 := by
    simpa [prefixWord, tailWord_39532, baseEnd_39532] using wordTrace_append hprefix tailTrace_39532
  have hstable : (prefixWord ++ tailWord_39532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39532).length < 2 ^ (prefixWord ++ tailWord_39532).sum := by decide
  have hdescent : baseEnd_39532 < baseStart_39532 := by decide
  rcases family_descends (prefixWord ++ tailWord_39532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39534 : List Nat := [4, 1, 2, 2, 2, 2, 3, 6]
def baseStart_39534 : Nat := 118140960795 + 39534 * 2 ^ 59
def prefixEnd_39534 : Nat := 4983230072969 + 3 ^ 40 * 39534 * 2
def baseEnd_39534 : Nat := 1503699569996559758755

theorem tailTrace_39534 : CollatzResearch.WordTrace tailWord_39534 prefixEnd_39534 1503699569996559758755 := by
  unfold tailWord_39534
  simp only [CollatzResearch.WordTrace]
  refine ⟨180240429847818089345707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 961282292521696476510437 180240429847818089345707)
  ·
    refine ⟨270360644771727134018561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180240429847818089345707 270360644771727134018561)
    ·
      refine ⟨202770483578795350513921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270360644771727134018561 202770483578795350513921)
      ·
        refine ⟨152077862684096512885441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202770483578795350513921 152077862684096512885441)
        ·
          refine ⟨114058397013072384664081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152077862684096512885441 114058397013072384664081)
          ·
            refine ⟨85543797759804288498061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114058397013072384664081 85543797759804288498061)
            ·
              refine ⟨32078924159926608186773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85543797759804288498061 32078924159926608186773)
              ·
                refine ⟨1503699569996559758755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32078924159926608186773 1503699569996559758755)
                ·
                  rfl

theorem cell22_39534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_39534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39534 prefixEnd_39534 := by exact prefixLift 39534
  have htrace : WordTrace (prefixWord ++ tailWord_39534) baseStart_39534 baseEnd_39534 := by
    simpa [prefixWord, tailWord_39534, baseEnd_39534] using wordTrace_append hprefix tailTrace_39534
  have hstable : (prefixWord ++ tailWord_39534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39534).length < 2 ^ (prefixWord ++ tailWord_39534).sum := by decide
  have hdescent : baseEnd_39534 < baseStart_39534 := by decide
  rcases family_descends (prefixWord ++ tailWord_39534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39536 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_39536 : Nat := 118140960795 + 39536 * 2 ^ 59
def prefixEnd_39536 : Nat := 4983230072969 + 3 ^ 40 * 39536 * 2
def baseEnd_39536 : Nat := 13533980770841699278789

theorem tailTrace_39536 : CollatzResearch.WordTrace tailWord_39536 prefixEnd_39536 13533980770841699278789 := by
  unfold tailWord_39536
  simp only [CollatzResearch.WordTrace]
  refine ⟨720998192387649528169231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 961330923183532704225641 720998192387649528169231)
  ·
    refine ⟨1081497288581474292253847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720998192387649528169231 1081497288581474292253847)
    ·
      refine ⟨1622245932872211438380771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1081497288581474292253847 1622245932872211438380771)
      ·
        refine ⟨2433368899308317157571157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622245932872211438380771 2433368899308317157571157)
        ·
          refine ⟨28516041788769341690287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 2433368899308317157571157 28516041788769341690287)
          ·
            refine ⟨42774062683154012535431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28516041788769341690287 42774062683154012535431)
            ·
              refine ⟨64161094024731018803147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42774062683154012535431 64161094024731018803147)
              ·
                refine ⟨96241641037096528204721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64161094024731018803147 96241641037096528204721)
                ·
                  refine ⟨72181230777822396153541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96241641037096528204721 72181230777822396153541)
                  ·
                    refine ⟨13533980770841699278789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72181230777822396153541 13533980770841699278789)
                    ·
                      rfl

theorem cell22_39536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_39536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39536 prefixEnd_39536 := by exact prefixLift 39536
  have htrace : WordTrace (prefixWord ++ tailWord_39536) baseStart_39536 baseEnd_39536 := by
    simpa [prefixWord, tailWord_39536, baseEnd_39536] using wordTrace_append hprefix tailTrace_39536
  have hstable : (prefixWord ++ tailWord_39536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39536).length < 2 ^ (prefixWord ++ tailWord_39536).sum := by decide
  have hdescent : baseEnd_39536 < baseStart_39536 := by decide
  rcases family_descends (prefixWord ++ tailWord_39536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39566 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_39566 : Nat := 118140960795 + 39566 * 2 ^ 59
def prefixEnd_39566 : Nat := 4983230072969 + 3 ^ 40 * 39566 * 2
def baseEnd_39566 : Nat := 13544250383931621028697

theorem tailTrace_39566 : CollatzResearch.WordTrace tailWord_39566 prefixEnd_39566 13544250383931621028697 := by
  unfold tailWord_39566
  simp only [CollatzResearch.WordTrace]
  refine ⟨180386321833326772491319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 962060383111076119953701 180386321833326772491319)
  ·
    refine ⟨270579482749990158736979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180386321833326772491319 270579482749990158736979)
    ·
      refine ⟨405869224124985238105469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270579482749990158736979 405869224124985238105469)
      ·
        refine ⟨152200959046869464289551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405869224124985238105469 152200959046869464289551)
        ·
          refine ⟨228301438570304196434327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152200959046869464289551 228301438570304196434327)
          ·
            refine ⟨342452157855456294651491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228301438570304196434327 342452157855456294651491)
            ·
              refine ⟨513678236783184441977237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342452157855456294651491 513678236783184441977237)
              ·
                refine ⟨24078667349211770717683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 513678236783184441977237 24078667349211770717683)
                ·
                  refine ⟨36118001023817656076525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24078667349211770717683 36118001023817656076525)
                  ·
                    refine ⟨13544250383931621028697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36118001023817656076525 13544250383931621028697)
                    ·
                      rfl

theorem cell22_39566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_39566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39566 prefixEnd_39566 := by exact prefixLift 39566
  have htrace : WordTrace (prefixWord ++ tailWord_39566) baseStart_39566 baseEnd_39566 := by
    simpa [prefixWord, tailWord_39566, baseEnd_39566] using wordTrace_append hprefix tailTrace_39566
  have hstable : (prefixWord ++ tailWord_39566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39566).length < 2 ^ (prefixWord ++ tailWord_39566).sum := by decide
  have hdescent : baseEnd_39566 < baseStart_39566 := by decide
  rcases family_descends (prefixWord ++ tailWord_39566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39617 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 1, 3]
def baseStart_39617 : Nat := 118140960795 + 39617 * 2 ^ 59
def prefixEnd_39617 : Nat := 4983230072969 + 3 ^ 40 * 39617 * 2
def baseEnd_39617 : Nat := 13561708726184488003541

theorem tailTrace_39617 : CollatzResearch.WordTrace tailWord_39617 prefixEnd_39617 13561708726184488003541 := by
  unfold tailWord_39617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444950697481849890037105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 963300464987899926691403 1444950697481849890037105)
  ·
    refine ⟨1083713023111387417527829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1444950697481849890037105 1083713023111387417527829)
    ·
      refine ⟨50799047958346285196617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1083713023111387417527829 50799047958346285196617)
      ·
        refine ⟨38099285968759713897463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50799047958346285196617 38099285968759713897463)
        ·
          refine ⟨57148928953139570846195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38099285968759713897463 57148928953139570846195)
          ·
            refine ⟨85723393429709356269293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57148928953139570846195 85723393429709356269293)
            ·
              refine ⟨32146272536141008600985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85723393429709356269293 32146272536141008600985)
              ·
                refine ⟨24109704402105756450739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32146272536141008600985 24109704402105756450739)
                ·
                  refine ⟨36164556603158634676109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24109704402105756450739 36164556603158634676109)
                  ·
                    refine ⟨13561708726184488003541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36164556603158634676109 13561708726184488003541)
                    ·
                      rfl

theorem cell22_39617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_39617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39617 prefixEnd_39617 := by exact prefixLift 39617
  have htrace : WordTrace (prefixWord ++ tailWord_39617) baseStart_39617 baseEnd_39617 := by
    simpa [prefixWord, tailWord_39617, baseEnd_39617] using wordTrace_append hprefix tailTrace_39617
  have hstable : (prefixWord ++ tailWord_39617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39617).length < 2 ^ (prefixWord ++ tailWord_39617).sum := by decide
  have hdescent : baseEnd_39617 < baseStart_39617 := by decide
  rcases family_descends (prefixWord ++ tailWord_39617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39624 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_39624 : Nat := 118140960795 + 39624 * 2 ^ 59
def prefixEnd_39624 : Nat := 4983230072969 + 3 ^ 40 * 39624 * 2
def baseEnd_39624 : Nat := 4521368323079601026173

theorem tailTrace_39624 : CollatzResearch.WordTrace tailWord_39624 prefixEnd_39624 4521368323079601026173 := by
  unfold tailWord_39624
  simp only [CollatzResearch.WordTrace]
  refine ⟨722603004228245042770963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 963470672304326723694617 722603004228245042770963)
  ·
    refine ⟨1083904506342367564156445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722603004228245042770963 1083904506342367564156445)
    ·
      refine ⟨406464189878387836558667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1083904506342367564156445 406464189878387836558667)
      ·
        refine ⟨609696284817581754838001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406464189878387836558667 609696284817581754838001)
        ·
          refine ⟨457272213613186316128501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609696284817581754838001 457272213613186316128501)
          ·
            refine ⟨42869270026236217137047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 457272213613186316128501 42869270026236217137047)
            ·
              refine ⟨64303905039354325705571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42869270026236217137047 64303905039354325705571)
              ·
                refine ⟨96455857559031488558357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64303905039354325705571 96455857559031488558357)
                ·
                  refine ⟨4521368323079601026173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96455857559031488558357 4521368323079601026173)
                  ·
                    rfl

theorem cell22_39624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_39624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39624 prefixEnd_39624 := by exact prefixLift 39624
  have htrace : WordTrace (prefixWord ++ tailWord_39624) baseStart_39624 baseEnd_39624 := by
    simpa [prefixWord, tailWord_39624, baseEnd_39624] using wordTrace_append hprefix tailTrace_39624
  have hstable : (prefixWord ++ tailWord_39624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39624).length < 2 ^ (prefixWord ++ tailWord_39624).sum := by decide
  have hdescent : baseEnd_39624 < baseStart_39624 := by decide
  rcases family_descends (prefixWord ++ tailWord_39624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39652 : List Nat := [2, 3, 1, 1, 1, 4, 2, 8]
def baseStart_39652 : Nat := 118140960795 + 39652 * 2 ^ 59
def prefixEnd_39652 : Nat := 4983230072969 + 3 ^ 40 * 39652 * 2
def baseEnd_39652 : Nat := 1508187771272895930937

theorem tailTrace_39652 : CollatzResearch.WordTrace tailWord_39652 prefixEnd_39652 1508187771272895930937 := by
  unfold tailWord_39652
  simp only [CollatzResearch.WordTrace]
  refine ⟨723113626177525433780605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 964151501570033911707473 723113626177525433780605)
  ·
    refine ⟨271167609816572037667727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 723113626177525433780605 271167609816572037667727)
    ·
      refine ⟨406751414724858056501591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271167609816572037667727 406751414724858056501591)
      ·
        refine ⟨610127122087287084752387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406751414724858056501591 610127122087287084752387)
        ·
          refine ⟨915190683130930627128581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610127122087287084752387 915190683130930627128581)
          ·
            refine ⟨171598253087049492586609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 915190683130930627128581 171598253087049492586609)
            ·
              refine ⟨128698689815287119439957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171598253087049492586609 128698689815287119439957)
              ·
                refine ⟨1508187771272895930937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128698689815287119439957 1508187771272895930937)
                ·
                  rfl

theorem cell22_39652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_39652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39652 prefixEnd_39652 := by exact prefixLift 39652
  have htrace : WordTrace (prefixWord ++ tailWord_39652) baseStart_39652 baseEnd_39652 := by
    simpa [prefixWord, tailWord_39652, baseEnd_39652] using wordTrace_append hprefix tailTrace_39652
  have hstable : (prefixWord ++ tailWord_39652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39652).length < 2 ^ (prefixWord ++ tailWord_39652).sum := by decide
  have hdescent : baseEnd_39652 < baseStart_39652 := by decide
  rcases family_descends (prefixWord ++ tailWord_39652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39731 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 5]
def baseStart_39731 : Nat := 118140960795 + 39731 * 2 ^ 59
def prefixEnd_39731 : Nat := 4983230072969 + 3 ^ 40 * 39731 * 2
def baseEnd_39731 : Nat := 4533577751975396884397

theorem tailTrace_39731 : CollatzResearch.WordTrace tailWord_39731 prefixEnd_39731 4533577751975396884397 := by
  unfold tailWord_39731
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449108619068847359687047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 966072412712564906458031 1449108619068847359687047)
  ·
    refine ⟨2173662928603271039530571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449108619068847359687047 2173662928603271039530571)
    ·
      refine ⟨3260494392904906559295857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173662928603271039530571 3260494392904906559295857)
      ·
        refine ⟨2445370794678679919471893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3260494392904906559295857 2445370794678679919471893)
        ·
          refine ⟨114626756000563121225245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2445370794678679919471893 114626756000563121225245)
          ·
            refine ⟨42985033500211170459467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114626756000563121225245 42985033500211170459467)
            ·
              refine ⟨64477550250316755689201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42985033500211170459467 64477550250316755689201)
              ·
                refine ⟨48358162687737566766901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64477550250316755689201 48358162687737566766901)
                ·
                  refine ⟨4533577751975396884397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48358162687737566766901 4533577751975396884397)
                  ·
                    rfl

theorem cell22_39731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 5].length) (baseStart_39731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39731 prefixEnd_39731 := by exact prefixLift 39731
  have htrace : WordTrace (prefixWord ++ tailWord_39731) baseStart_39731 baseEnd_39731 := by
    simpa [prefixWord, tailWord_39731, baseEnd_39731] using wordTrace_append hprefix tailTrace_39731
  have hstable : (prefixWord ++ tailWord_39731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39731).length < 2 ^ (prefixWord ++ tailWord_39731).sum := by decide
  have hdescent : baseEnd_39731 < baseStart_39731 := by decide
  rcases family_descends (prefixWord ++ tailWord_39731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39787 : List Nat := [1, 1, 1, 1, 2, 2, 14]
def baseStart_39787 : Nat := 118140960795 + 39787 * 2 ^ 59
def prefixEnd_39787 : Nat := 4983230072969 + 3 ^ 40 * 39787 * 2
def baseEnd_39787 : Nat := 504440859272618935297

theorem tailTrace_39787 : CollatzResearch.WordTrace tailWord_39787 prefixEnd_39787 504440859272618935297 := by
  unfold tailWord_39787
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451151106865968923725615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 967434071243979282483743 1451151106865968923725615)
  ·
    refine ⟨2176726660298953385588423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1451151106865968923725615 2176726660298953385588423)
    ·
      refine ⟨3265089990448430078382635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176726660298953385588423 3265089990448430078382635)
      ·
        refine ⟨4897634985672645117573953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265089990448430078382635 4897634985672645117573953)
        ·
          refine ⟨3673226239254483838180465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4897634985672645117573953 3673226239254483838180465)
          ·
            refine ⟨2754919679440862878635349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673226239254483838180465 2754919679440862878635349)
            ·
              refine ⟨504440859272618935297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 2754919679440862878635349 504440859272618935297)
              ·
                rfl

theorem cell22_39787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 14].length) (baseStart_39787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39787 prefixEnd_39787 := by exact prefixLift 39787
  have htrace : WordTrace (prefixWord ++ tailWord_39787) baseStart_39787 baseEnd_39787 := by
    simpa [prefixWord, tailWord_39787, baseEnd_39787] using wordTrace_append hprefix tailTrace_39787
  have hstable : (prefixWord ++ tailWord_39787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39787).length < 2 ^ (prefixWord ++ tailWord_39787).sum := by decide
  have hdescent : baseEnd_39787 < baseStart_39787 := by decide
  rcases family_descends (prefixWord ++ tailWord_39787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39793 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 4]
def baseStart_39793 : Nat := 118140960795 + 39793 * 2 ^ 59
def prefixEnd_39793 : Nat := 4983230072969 + 3 ^ 40 * 39793 * 2
def baseEnd_39793 : Nat := 4540652374326231867667

theorem tailTrace_39793 : CollatzResearch.WordTrace tailWord_39793 prefixEnd_39793 4540652374326231867667 := by
  unfold tailWord_39793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451369944844231948444033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 967579963229487965629355 1451369944844231948444033)
  ·
    refine ⟨1088527458633173961333025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1451369944844231948444033 1088527458633173961333025)
    ·
      refine ⟨816395593974880470999769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1088527458633173961333025 816395593974880470999769)
      ·
        refine ⟨612296695481160353249827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816395593974880470999769 612296695481160353249827)
        ·
          refine ⟨918445043221740529874741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612296695481160353249827 918445043221740529874741)
          ·
            refine ⟨86104222802038174675757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 918445043221740529874741 86104222802038174675757)
            ·
              refine ⟨32289083550764315503409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86104222802038174675757 32289083550764315503409)
              ·
                refine ⟨24216812663073236627557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32289083550764315503409 24216812663073236627557)
                ·
                  refine ⟨4540652374326231867667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24216812663073236627557 4540652374326231867667)
                  ·
                    rfl

theorem cell22_39793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_39793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39793 prefixEnd_39793 := by exact prefixLift 39793
  have htrace : WordTrace (prefixWord ++ tailWord_39793) baseStart_39793 baseEnd_39793 := by
    simpa [prefixWord, tailWord_39793, baseEnd_39793] using wordTrace_append hprefix tailTrace_39793
  have hstable : (prefixWord ++ tailWord_39793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39793).length < 2 ^ (prefixWord ++ tailWord_39793).sum := by decide
  have hdescent : baseEnd_39793 < baseStart_39793 := by decide
  rcases family_descends (prefixWord ++ tailWord_39793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39864 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_39864 : Nat := 118140960795 + 39864 * 2 ^ 59
def prefixEnd_39864 : Nat := 4983230072969 + 3 ^ 40 * 39864 * 2
def baseEnd_39864 : Nat := 13646261873958177077783

theorem tailTrace_39864 : CollatzResearch.WordTrace tailWord_39864 prefixEnd_39864 13646261873958177077783 := by
  unfold tailWord_39864
  simp only [CollatzResearch.WordTrace]
  refine ⟨726979763793505537139323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 969306351724674049519097 726979763793505537139323)
  ·
    refine ⟨1090469645690258305708985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 726979763793505537139323 1090469645690258305708985)
    ·
      refine ⟨817852234267693729281739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090469645690258305708985 817852234267693729281739)
      ·
        refine ⟨1226778351401540593922609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817852234267693729281739 1226778351401540593922609)
        ·
          refine ⟨920083763551155445441957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226778351401540593922609 920083763551155445441957)
          ·
            refine ⟨172515705665841646020367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 920083763551155445441957 172515705665841646020367)
            ·
              refine ⟨258773558498762469030551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172515705665841646020367 258773558498762469030551)
              ·
                refine ⟨388160337748143703545827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258773558498762469030551 388160337748143703545827)
                ·
                  refine ⟨582240506622215555318741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388160337748143703545827 582240506622215555318741)
                  ·
                    refine ⟨13646261873958177077783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 582240506622215555318741 13646261873958177077783)
                    ·
                      rfl

theorem cell22_39864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_39864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39864 prefixEnd_39864 := by exact prefixLift 39864
  have htrace : WordTrace (prefixWord ++ tailWord_39864) baseStart_39864 baseEnd_39864 := by
    simpa [prefixWord, tailWord_39864, baseEnd_39864] using wordTrace_append hprefix tailTrace_39864
  have hstable : (prefixWord ++ tailWord_39864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39864).length < 2 ^ (prefixWord ++ tailWord_39864).sum := by decide
  have hdescent : baseEnd_39864 < baseStart_39864 := by decide
  rcases family_descends (prefixWord ++ tailWord_39864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39911 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 6]
def baseStart_39911 : Nat := 118140960795 + 39911 * 2 ^ 59
def prefixEnd_39911 : Nat := 4983230072969 + 3 ^ 40 * 39911 * 2
def baseEnd_39911 : Nat := 4554116978155240384213

theorem tailTrace_39911 : CollatzResearch.WordTrace tailWord_39911 prefixEnd_39911 4554116978155240384213 := by
  unfold tailWord_39911
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455673758416738101239587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 970449172277825400826391 1455673758416738101239587)
  ·
    refine ⟨2183510637625107151859381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1455673758416738101239587 2183510637625107151859381)
    ·
      refine ⟨204704122277353795486817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2183510637625107151859381 204704122277353795486817)
      ·
        refine ⟨153528091708015346615113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204704122277353795486817 153528091708015346615113)
        ·
          refine ⟨115146068781011509961335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153528091708015346615113 115146068781011509961335)
          ·
            refine ⟨172719103171517264942003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115146068781011509961335 172719103171517264942003)
            ·
              refine ⟨259078654757275897413005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172719103171517264942003 259078654757275897413005)
              ·
                refine ⟨97154495533978461529877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259078654757275897413005 97154495533978461529877)
                ·
                  refine ⟨4554116978155240384213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97154495533978461529877 4554116978155240384213)
                  ·
                    rfl

theorem cell22_39911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_39911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39911 prefixEnd_39911 := by exact prefixLift 39911
  have htrace : WordTrace (prefixWord ++ tailWord_39911) baseStart_39911 baseEnd_39911 := by
    simpa [prefixWord, tailWord_39911, baseEnd_39911] using wordTrace_append hprefix tailTrace_39911
  have hstable : (prefixWord ++ tailWord_39911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39911).length < 2 ^ (prefixWord ++ tailWord_39911).sum := by decide
  have hdescent : baseEnd_39911 < baseStart_39911 := by decide
  rcases family_descends (prefixWord ++ tailWord_39911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39941 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_39941 : Nat := 118140960795 + 39941 * 2 ^ 59
def prefixEnd_39941 : Nat := 4983230072969 + 3 ^ 40 * 39941 * 2
def baseEnd_39941 : Nat := 13672620547555642902547

theorem tailTrace_39941 : CollatzResearch.WordTrace tailWord_39941 prefixEnd_39941 13672620547555642902547 := by
  unfold tailWord_39941
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456767948308053224831677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 971178632205368816554451 1456767948308053224831677)
  ·
    refine ⟨546287980615519959311879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1456767948308053224831677 546287980615519959311879)
    ·
      refine ⟨819431970923279938967819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546287980615519959311879 819431970923279938967819)
      ·
        refine ⟨1229147956384919908451729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819431970923279938967819 1229147956384919908451729)
        ·
          refine ⟨921860967288689931338797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229147956384919908451729 921860967288689931338797)
          ·
            refine ⟨345697862733258724252049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 921860967288689931338797 345697862733258724252049)
            ·
              refine ⟨259273397049944043189037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345697862733258724252049 259273397049944043189037)
              ·
                refine ⟨97227523893729016195889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259273397049944043189037 97227523893729016195889)
                ·
                  refine ⟨72920642920296762146917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97227523893729016195889 72920642920296762146917)
                  ·
                    refine ⟨13672620547555642902547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72920642920296762146917 13672620547555642902547)
                    ·
                      rfl

theorem cell22_39941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_39941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_39941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_39941 prefixEnd_39941 := by exact prefixLift 39941
  have htrace : WordTrace (prefixWord ++ tailWord_39941) baseStart_39941 baseEnd_39941 := by
    simpa [prefixWord, tailWord_39941, baseEnd_39941] using wordTrace_append hprefix tailTrace_39941
  have hstable : (prefixWord ++ tailWord_39941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39941).length < 2 ^ (prefixWord ++ tailWord_39941).sum := by decide
  have hdescent : baseEnd_39941 < baseStart_39941 := by decide
  rcases family_descends (prefixWord ++ tailWord_39941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40018 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_40018 : Nat := 118140960795 + 40018 * 2 ^ 59
def prefixEnd_40018 : Nat := 4983230072969 + 3 ^ 40 * 40018 * 2
def baseEnd_40018 : Nat := 4566326407051036242437

theorem tailTrace_40018 : CollatzResearch.WordTrace tailWord_40018 prefixEnd_40018 4566326407051036242437 := by
  unfold tailWord_40018
  simp only [CollatzResearch.WordTrace]
  refine ⟨364894092257273843846177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 973050912686063583589805 364894092257273843846177)
  ·
    refine ⟨273670569192955382884633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 364894092257273843846177 273670569192955382884633)
    ·
      refine ⟨205252926894716537163475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273670569192955382884633 205252926894716537163475)
      ·
        refine ⟨307879390342074805745213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205252926894716537163475 307879390342074805745213)
        ·
          refine ⟨115454771378278052154455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307879390342074805745213 115454771378278052154455)
          ·
            refine ⟨173182157067417078231683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115454771378278052154455 173182157067417078231683)
            ·
              refine ⟨259773235601125617347525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173182157067417078231683 259773235601125617347525)
              ·
                refine ⟨48707481675211053252661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259773235601125617347525 48707481675211053252661)
                ·
                  refine ⟨4566326407051036242437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48707481675211053252661 4566326407051036242437)
                  ·
                    rfl

theorem cell22_40018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_40018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40018 prefixEnd_40018 := by exact prefixLift 40018
  have htrace : WordTrace (prefixWord ++ tailWord_40018) baseStart_40018 baseEnd_40018 := by
    simpa [prefixWord, tailWord_40018, baseEnd_40018] using wordTrace_append hprefix tailTrace_40018
  have hstable : (prefixWord ++ tailWord_40018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40018).length < 2 ^ (prefixWord ++ tailWord_40018).sum := by decide
  have hdescent : baseEnd_40018 < baseStart_40018 := by decide
  rcases family_descends (prefixWord ++ tailWord_40018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40031 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_40031 : Nat := 118140960795 + 40031 * 2 ^ 59
def prefixEnd_40031 : Nat := 4983230072969 + 3 ^ 40 * 40031 * 2
def baseEnd_40031 : Nat := 13703429386825408152271

theorem tailTrace_40031 : CollatzResearch.WordTrace tailWord_40031 prefixEnd_40031 13703429386825408152271 := by
  unfold tailWord_40031
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460050517981998595607947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 973367011987999063738631 1460050517981998595607947)
  ·
    refine ⟨2190075776972997893411921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460050517981998595607947 2190075776972997893411921)
    ·
      refine ⟨1642556832729748420058941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2190075776972997893411921 1642556832729748420058941)
      ·
        refine ⟨615958812273655657522103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1642556832729748420058941 615958812273655657522103)
        ·
          refine ⟨923938218410483486283155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615958812273655657522103 923938218410483486283155)
          ·
            refine ⟨1385907327615725229424733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923938218410483486283155 1385907327615725229424733)
            ·
              refine ⟨519715247855896961034275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385907327615725229424733 519715247855896961034275)
              ·
                refine ⟨779572871783845441551413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519715247855896961034275 779572871783845441551413)
                ·
                  refine ⟨73084956729735510145445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779572871783845441551413 73084956729735510145445)
                  ·
                    refine ⟨13703429386825408152271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73084956729735510145445 13703429386825408152271)
                    ·
                      rfl

theorem cell22_40031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_40031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40031 prefixEnd_40031 := by exact prefixLift 40031
  have htrace : WordTrace (prefixWord ++ tailWord_40031) baseStart_40031 baseEnd_40031 := by
    simpa [prefixWord, tailWord_40031, baseEnd_40031] using wordTrace_append hprefix tailTrace_40031
  have hstable : (prefixWord ++ tailWord_40031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40031).length < 2 ^ (prefixWord ++ tailWord_40031).sum := by decide
  have hdescent : baseEnd_40031 < baseStart_40031 := by decide
  rcases family_descends (prefixWord ++ tailWord_40031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40048 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_40048 : Nat := 118140960795 + 40048 * 2 ^ 59
def prefixEnd_40048 : Nat := 4983230072969 + 3 ^ 40 * 40048 * 2
def baseEnd_40048 : Nat := 13709248834243030477219

theorem tailTrace_40048 : CollatzResearch.WordTrace tailWord_40048 prefixEnd_40048 13709248834243030477219 := by
  unfold tailWord_40048
  simp only [CollatzResearch.WordTrace]
  refine ⟨730335279460205249488399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 973780372613606999317865 730335279460205249488399)
  ·
    refine ⟨1095502919190307874232599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730335279460205249488399 1095502919190307874232599)
    ·
      refine ⟨1643254378785461811348899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095502919190307874232599 1643254378785461811348899)
      ·
        refine ⟨2464881568178192717023349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643254378785461811348899 2464881568178192717023349)
        ·
          refine ⟨231082647016705567220939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2464881568178192717023349 231082647016705567220939)
          ·
            refine ⟨346623970525058350831409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231082647016705567220939 346623970525058350831409)
            ·
              refine ⟨259967977893793763123557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346623970525058350831409 259967977893793763123557)
              ·
                refine ⟨48743995855086330585667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259967977893793763123557 48743995855086330585667)
                ·
                  refine ⟨73115993782629495878501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48743995855086330585667 73115993782629495878501)
                  ·
                    refine ⟨13709248834243030477219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73115993782629495878501 13709248834243030477219)
                    ·
                      rfl

theorem cell22_40048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_40048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40048 prefixEnd_40048 := by exact prefixLift 40048
  have htrace : WordTrace (prefixWord ++ tailWord_40048) baseStart_40048 baseEnd_40048 := by
    simpa [prefixWord, tailWord_40048, baseEnd_40048] using wordTrace_append hprefix tailTrace_40048
  have hstable : (prefixWord ++ tailWord_40048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40048).length < 2 ^ (prefixWord ++ tailWord_40048).sum := by decide
  have hdescent : baseEnd_40048 < baseStart_40048 := by decide
  rcases family_descends (prefixWord ++ tailWord_40048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40065 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_40065 : Nat := 118140960795 + 40065 * 2 ^ 59
def prefixEnd_40065 : Nat := 4983230072969 + 3 ^ 40 * 40065 * 2
def baseEnd_40065 : Nat := 13715068281660652802167

theorem tailTrace_40065 : CollatzResearch.WordTrace tailWord_40065 prefixEnd_40065 13715068281660652802167 := by
  unfold tailWord_40065
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461290599858822402345649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 974193733239214934897099 1461290599858822402345649)
  ·
    refine ⟨1095967949894116801759237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1461290599858822402345649 1095967949894116801759237)
    ·
      refine ⟨205493990605146900329857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1095967949894116801759237 205493990605146900329857)
      ·
        refine ⟨154120492953860175247393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205493990605146900329857 154120492953860175247393)
        ·
          refine ⟨115590369715395131435545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154120492953860175247393 115590369715395131435545)
          ·
            refine ⟨86692777286546348576659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115590369715395131435545 86692777286546348576659)
            ·
              refine ⟨130039165929819522864989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86692777286546348576659 130039165929819522864989)
              ·
                refine ⟨48764687223682321074371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130039165929819522864989 48764687223682321074371)
                ·
                  refine ⟨73147030835523481611557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48764687223682321074371 73147030835523481611557)
                  ·
                    refine ⟨13715068281660652802167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73147030835523481611557 13715068281660652802167)
                    ·
                      rfl

theorem cell22_40065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_40065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40065 prefixEnd_40065 := by exact prefixLift 40065
  have htrace : WordTrace (prefixWord ++ tailWord_40065) baseStart_40065 baseEnd_40065 := by
    simpa [prefixWord, tailWord_40065, baseEnd_40065] using wordTrace_append hprefix tailTrace_40065
  have hstable : (prefixWord ++ tailWord_40065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40065).length < 2 ^ (prefixWord ++ tailWord_40065).sum := by decide
  have hdescent : baseEnd_40065 < baseStart_40065 := by decide
  rcases family_descends (prefixWord ++ tailWord_40065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40232 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_40232 : Nat := 118140960795 + 40232 * 2 ^ 59
def prefixEnd_40232 : Nat := 4983230072969 + 3 ^ 40 * 40232 * 2
def baseEnd_40232 : Nat := 4590745264842627958885

theorem tailTrace_40232 : CollatzResearch.WordTrace tailWord_40232 prefixEnd_40232 4590745264842627958885 := by
  unfold tailWord_40232
  simp only [CollatzResearch.WordTrace]
  refine ⟨733690795126904961837475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 978254393502539949116633 733690795126904961837475)
  ·
    refine ⟨1100536192690357442756213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733690795126904961837475 1100536192690357442756213)
    ·
      refine ⟨103175268064721010258395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1100536192690357442756213 103175268064721010258395)
      ·
        refine ⟨154762902097081515387593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103175268064721010258395 154762902097081515387593)
        ·
          refine ⟨116072176572811136540695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154762902097081515387593 116072176572811136540695)
          ·
            refine ⟨174108264859216704811043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116072176572811136540695 174108264859216704811043)
            ·
              refine ⟨261162397288825057216565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174108264859216704811043 261162397288825057216565)
              ·
                refine ⟨24483974745827349114053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261162397288825057216565 24483974745827349114053)
                ·
                  refine ⟨4590745264842627958885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24483974745827349114053 4590745264842627958885)
                  ·
                    rfl

theorem cell22_40232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_40232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40232 prefixEnd_40232 := by exact prefixLift 40232
  have htrace : WordTrace (prefixWord ++ tailWord_40232) baseStart_40232 baseEnd_40232 := by
    simpa [prefixWord, tailWord_40232, baseEnd_40232] using wordTrace_append hprefix tailTrace_40232
  have hstable : (prefixWord ++ tailWord_40232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40232).length < 2 ^ (prefixWord ++ tailWord_40232).sum := by decide
  have hdescent : baseEnd_40232 < baseStart_40232 := by decide
  rcases family_descends (prefixWord ++ tailWord_40232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40234 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_40234 : Nat := 118140960795 + 40234 * 2 ^ 59
def prefixEnd_40234 : Nat := 4983230072969 + 3 ^ 40 * 40234 * 2
def baseEnd_40234 : Nat := 13772920435400545326649

theorem tailTrace_40234 : CollatzResearch.WordTrace tailWord_40234 prefixEnd_40234 13772920435400545326649 := by
  unfold tailWord_40234
  simp only [CollatzResearch.WordTrace]
  refine ⟨366863634061641066311939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 978303024164376176831837 366863634061641066311939)
  ·
    refine ⟨550295451092461599467909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366863634061641066311939 550295451092461599467909)
    ·
      refine ⟨103180397079836549900233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 550295451092461599467909 103180397079836549900233)
      ·
        refine ⟨77385297809877412425175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103180397079836549900233 77385297809877412425175)
        ·
          refine ⟨116077946714816118637763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77385297809877412425175 116077946714816118637763)
          ·
            refine ⟨174116920072224177956645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116077946714816118637763 174116920072224177956645)
            ·
              refine ⟨32646922513542033366871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174116920072224177956645 32646922513542033366871)
              ·
                refine ⟨48970383770313050050307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32646922513542033366871 48970383770313050050307)
                ·
                  refine ⟨73455575655469575075461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48970383770313050050307 73455575655469575075461)
                  ·
                    refine ⟨13772920435400545326649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73455575655469575075461 13772920435400545326649)
                    ·
                      rfl

theorem cell22_40234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_40234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40234 prefixEnd_40234 := by exact prefixLift 40234
  have htrace : WordTrace (prefixWord ++ tailWord_40234) baseStart_40234 baseEnd_40234 := by
    simpa [prefixWord, tailWord_40234, baseEnd_40234] using wordTrace_append hprefix tailTrace_40234
  have hstable : (prefixWord ++ tailWord_40234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40234).length < 2 ^ (prefixWord ++ tailWord_40234).sum := by decide
  have hdescent : baseEnd_40234 < baseStart_40234 := by decide
  rcases family_descends (prefixWord ++ tailWord_40234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40243 : List Nat := [1, 1, 1, 2, 5, 3, 9]
def baseStart_40243 : Nat := 118140960795 + 40243 * 2 ^ 59
def prefixEnd_40243 : Nat := 4983230072969 + 3 ^ 40 * 40243 * 2
def baseEnd_40243 : Nat := 510222271086204513023

theorem tailTrace_40243 : CollatzResearch.WordTrace tailWord_40243 prefixEnd_40243 510222271086204513023 := by
  unfold tailWord_40243
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467782793213958802325383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 978521862142639201550255 1467782793213958802325383)
  ·
    refine ⟨2201674189820938203488075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1467782793213958802325383 2201674189820938203488075)
    ·
      refine ⟨3302511284731407305232113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201674189820938203488075 3302511284731407305232113)
      ·
        refine ⟨2476883463548555478924085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3302511284731407305232113 2476883463548555478924085)
        ·
          refine ⟨232207824707677076149133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2476883463548555478924085 232207824707677076149133)
          ·
            refine ⟨87077934265378903555925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232207824707677076149133 87077934265378903555925)
            ·
              refine ⟨510222271086204513023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 87077934265378903555925 510222271086204513023)
              ·
                rfl

theorem cell22_40243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 9].length) (baseStart_40243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40243 prefixEnd_40243 := by exact prefixLift 40243
  have htrace : WordTrace (prefixWord ++ tailWord_40243) baseStart_40243 baseEnd_40243 := by
    simpa [prefixWord, tailWord_40243, baseEnd_40243] using wordTrace_append hprefix tailTrace_40243
  have hstable : (prefixWord ++ tailWord_40243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40243).length < 2 ^ (prefixWord ++ tailWord_40243).sum := by decide
  have hdescent : baseEnd_40243 < baseStart_40243 := by decide
  rcases family_descends (prefixWord ++ tailWord_40243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40275 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 3, 3]
def baseStart_40275 : Nat := 118140960795 + 40275 * 2 ^ 59
def prefixEnd_40275 : Nat := 4983230072969 + 3 ^ 40 * 40275 * 2
def baseEnd_40275 : Nat := 13786955573290105051523

theorem tailTrace_40275 : CollatzResearch.WordTrace tailWord_40275 prefixEnd_40275 13786955573290105051523 := by
  unfold tailWord_40275
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468949929098028267490279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 979299952732018844993519 1468949929098028267490279)
  ·
    refine ⟨2203424893647042401235419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468949929098028267490279 2203424893647042401235419)
    ·
      refine ⟨3305137340470563601853129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203424893647042401235419 3305137340470563601853129)
      ·
        refine ⟨2478853005352922701389847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305137340470563601853129 2478853005352922701389847)
        ·
          refine ⟨3718279508029384052084771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478853005352922701389847 3718279508029384052084771)
          ·
            refine ⟨5577419262044076078127157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718279508029384052084771 5577419262044076078127157)
            ·
              refine ⟨522883055816632132324421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5577419262044076078127157 522883055816632132324421)
              ·
                refine ⟨98040572965618524810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522883055816632132324421 98040572965618524810829)
                ·
                  refine ⟨36765214862106946804061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98040572965618524810829 36765214862106946804061)
                  ·
                    refine ⟨13786955573290105051523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36765214862106946804061 13786955573290105051523)
                    ·
                      rfl

theorem cell22_40275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 3].length) (baseStart_40275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40275 prefixEnd_40275 := by exact prefixLift 40275
  have htrace : WordTrace (prefixWord ++ tailWord_40275) baseStart_40275 baseEnd_40275 := by
    simpa [prefixWord, tailWord_40275, baseEnd_40275] using wordTrace_append hprefix tailTrace_40275
  have hstable : (prefixWord ++ tailWord_40275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40275).length < 2 ^ (prefixWord ++ tailWord_40275).sum := by decide
  have hdescent : baseEnd_40275 < baseStart_40275 := by decide
  rcases family_descends (prefixWord ++ tailWord_40275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40277 : List Nat := [1, 3, 2, 2, 3, 3, 2, 6]
def baseStart_40277 : Nat := 118140960795 + 40277 * 2 ^ 59
def prefixEnd_40277 : Nat := 4983230072969 + 3 ^ 40 * 40277 * 2
def baseEnd_40277 : Nat := 1531960023795862944613

theorem tailTrace_40277 : CollatzResearch.WordTrace tailWord_40277 prefixEnd_40277 1531960023795862944613 := by
  unfold tailWord_40277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469022875090782609063085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 979348583393855072708723 1469022875090782609063085)
  ·
    refine ⟨550883578159043478398657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1469022875090782609063085 550883578159043478398657)
    ·
      refine ⟨413162683619282608798993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 550883578159043478398657 413162683619282608798993)
      ·
        refine ⟨309872012714461956599245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413162683619282608798993 309872012714461956599245)
        ·
          refine ⟨116202004767923233724717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309872012714461956599245 116202004767923233724717)
          ·
            refine ⟨43575751787971212646769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116202004767923233724717 43575751787971212646769)
            ·
              refine ⟨32681813840978409485077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43575751787971212646769 32681813840978409485077)
              ·
                refine ⟨1531960023795862944613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32681813840978409485077 1531960023795862944613)
                ·
                  rfl

theorem cell22_40277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 6].length) (baseStart_40277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40277 prefixEnd_40277 := by exact prefixLift 40277
  have htrace : WordTrace (prefixWord ++ tailWord_40277) baseStart_40277 baseEnd_40277 := by
    simpa [prefixWord, tailWord_40277, baseEnd_40277] using wordTrace_append hprefix tailTrace_40277
  have hstable : (prefixWord ++ tailWord_40277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40277).length < 2 ^ (prefixWord ++ tailWord_40277).sum := by decide
  have hdescent : baseEnd_40277 < baseStart_40277 := by decide
  rcases family_descends (prefixWord ++ tailWord_40277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40360 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 1, 3]
def baseStart_40360 : Nat := 118140960795 + 40360 * 2 ^ 59
def prefixEnd_40360 : Nat := 4983230072969 + 3 ^ 40 * 40360 * 2
def baseEnd_40360 : Nat := 13816052810378216676263

theorem tailTrace_40360 : CollatzResearch.WordTrace tailWord_40360 prefixEnd_40360 13816052810378216676263 := by
  unfold tailWord_40360
  simp only [CollatzResearch.WordTrace]
  refine ⟨736025066895043892167267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 981366755860058522889689 736025066895043892167267)
  ·
    refine ⟨1104037600342565838250901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 736025066895043892167267 1104037600342565838250901)
    ·
      refine ⟨51751762516057773668011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1104037600342565838250901 51751762516057773668011)
      ·
        refine ⟨77627643774086660502017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51751762516057773668011 77627643774086660502017)
        ·
          refine ⟨58220732830564995376513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77627643774086660502017 58220732830564995376513)
          ·
            refine ⟨43665549622923746532385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58220732830564995376513 43665549622923746532385)
            ·
              refine ⟨32749162217192809899289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43665549622923746532385 32749162217192809899289)
              ·
                refine ⟨24561871662894607424467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32749162217192809899289 24561871662894607424467)
                ·
                  refine ⟨36842807494341911136701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24561871662894607424467 36842807494341911136701)
                  ·
                    refine ⟨13816052810378216676263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36842807494341911136701 13816052810378216676263)
                    ·
                      rfl

theorem cell22_40360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_40360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40360 prefixEnd_40360 := by exact prefixLift 40360
  have htrace : WordTrace (prefixWord ++ tailWord_40360) baseStart_40360 baseEnd_40360 := by
    simpa [prefixWord, tailWord_40360, baseEnd_40360] using wordTrace_append hprefix tailTrace_40360
  have hstable : (prefixWord ++ tailWord_40360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40360).length < 2 ^ (prefixWord ++ tailWord_40360).sum := by decide
  have hdescent : baseEnd_40360 < baseStart_40360 := by decide
  rcases family_descends (prefixWord ++ tailWord_40360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40382 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_40382 : Nat := 118140960795 + 40382 * 2 ^ 59
def prefixEnd_40382 : Nat := 4983230072969 + 3 ^ 40 * 40382 * 2
def baseEnd_40382 : Nat := 13823583859977492626195

theorem tailTrace_40382 : CollatzResearch.WordTrace tailWord_40382 prefixEnd_40382 13823583859977492626195 := by
  unfold tailWord_40382
  simp only [CollatzResearch.WordTrace]
  refine ⟨184106567463798192704425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 981901693140257027756933 184106567463798192704425)
  ·
    refine ⟨138079925597848644528319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184106567463798192704425 138079925597848644528319)
    ·
      refine ⟨207119888396772966792479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138079925597848644528319 207119888396772966792479)
      ·
        refine ⟨310679832595159450188719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207119888396772966792479 310679832595159450188719)
        ·
          refine ⟨466019748892739175283079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310679832595159450188719 466019748892739175283079)
          ·
            refine ⟨699029623339108762924619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466019748892739175283079 699029623339108762924619)
            ·
              refine ⟨1048544435008663144386929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699029623339108762924619 1048544435008663144386929)
              ·
                refine ⟨786408326256497358290197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048544435008663144386929 786408326256497358290197)
                ·
                  refine ⟨36862890293273313669853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 786408326256497358290197 36862890293273313669853)
                  ·
                    refine ⟨13823583859977492626195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36862890293273313669853 13823583859977492626195)
                    ·
                      rfl

theorem cell22_40382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_40382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40382 prefixEnd_40382 := by exact prefixLift 40382
  have htrace : WordTrace (prefixWord ++ tailWord_40382) baseStart_40382 baseEnd_40382 := by
    simpa [prefixWord, tailWord_40382, baseEnd_40382] using wordTrace_append hprefix tailTrace_40382
  have hstable : (prefixWord ++ tailWord_40382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40382).length < 2 ^ (prefixWord ++ tailWord_40382).sum := by decide
  have hdescent : baseEnd_40382 < baseStart_40382 := by decide
  rcases family_descends (prefixWord ++ tailWord_40382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40504 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_40504 : Nat := 118140960795 + 40504 * 2 ^ 59
def prefixEnd_40504 : Nat := 4983230072969 + 3 ^ 40 * 40504 * 2
def baseEnd_40504 : Nat := 13865346953209841075821

theorem tailTrace_40504 : CollatzResearch.WordTrace tailWord_40504 prefixEnd_40504 13865346953209841075821 := by
  unfold tailWord_40504
  simp only [CollatzResearch.WordTrace]
  refine ⟨738651122634200188788283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 984868163512266918384377 738651122634200188788283)
  ·
    refine ⟨1107976683951300283182425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738651122634200188788283 1107976683951300283182425)
    ·
      refine ⟨830982512963475212386819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107976683951300283182425 830982512963475212386819)
      ·
        refine ⟨1246473769445212818580229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830982512963475212386819 1246473769445212818580229)
        ·
          refine ⟨233713831770977403483793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1246473769445212818580229 233713831770977403483793)
          ·
            refine ⟨175285373828233052612845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233713831770977403483793 175285373828233052612845)
            ·
              refine ⟨65732015185587394729817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175285373828233052612845 65732015185587394729817)
              ·
                refine ⟨49299011389190546047363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65732015185587394729817 49299011389190546047363)
                ·
                  refine ⟨73948517083785819071045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49299011389190546047363 73948517083785819071045)
                  ·
                    refine ⟨13865346953209841075821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73948517083785819071045 13865346953209841075821)
                    ·
                      rfl

theorem cell22_40504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_40504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40504 prefixEnd_40504 := by exact prefixLift 40504
  have htrace : WordTrace (prefixWord ++ tailWord_40504) baseStart_40504 baseEnd_40504 := by
    simpa [prefixWord, tailWord_40504, baseEnd_40504] using wordTrace_append hprefix tailTrace_40504
  have hstable : (prefixWord ++ tailWord_40504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40504).length < 2 ^ (prefixWord ++ tailWord_40504).sum := by decide
  have hdescent : baseEnd_40504 < baseStart_40504 := by decide
  rcases family_descends (prefixWord ++ tailWord_40504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40517 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_40517 : Nat := 118140960795 + 40517 * 2 ^ 59
def prefixEnd_40517 : Nat := 4983230072969 + 3 ^ 40 * 40517 * 2
def baseEnd_40517 : Nat := 13869797118882140500781

theorem tailTrace_40517 : CollatzResearch.WordTrace tailWord_40517 prefixEnd_40517 13869797118882140500781 := by
  unfold tailWord_40517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477776394221303597799805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 985184262814202398533203 1477776394221303597799805)
  ·
    refine ⟨554166147832988849174927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1477776394221303597799805 554166147832988849174927)
    ·
      refine ⟨831249221749483273762391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554166147832988849174927 831249221749483273762391)
      ·
        refine ⟨1246873832624224910643587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831249221749483273762391 1246873832624224910643587)
        ·
          refine ⟨1870310748936337365965381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246873832624224910643587 1870310748936337365965381)
          ·
            refine ⟨350683265425563256118509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1870310748936337365965381 350683265425563256118509)
            ·
              refine ⟨131506224534586221044441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350683265425563256118509 131506224534586221044441)
              ·
                refine ⟨98629668400939665783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131506224534586221044441 98629668400939665783331)
                ·
                  refine ⟨147944502601409498674997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98629668400939665783331 147944502601409498674997)
                  ·
                    refine ⟨13869797118882140500781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147944502601409498674997 13869797118882140500781)
                    ·
                      rfl

theorem cell22_40517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_40517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40517 prefixEnd_40517 := by exact prefixLift 40517
  have htrace : WordTrace (prefixWord ++ tailWord_40517) baseStart_40517 baseEnd_40517 := by
    simpa [prefixWord, tailWord_40517, baseEnd_40517] using wordTrace_append hprefix tailTrace_40517
  have hstable : (prefixWord ++ tailWord_40517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40517).length < 2 ^ (prefixWord ++ tailWord_40517).sum := by decide
  have hdescent : baseEnd_40517 < baseStart_40517 := by decide
  rcases family_descends (prefixWord ++ tailWord_40517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40547 : List Nat := [1, 1, 1, 5, 1, 3, 3, 7]
def baseStart_40547 : Nat := 118140960795 + 40547 * 2 ^ 59
def prefixEnd_40547 : Nat := 4983230072969 + 3 ^ 40 * 40547 * 2
def baseEnd_40547 : Nat := 1542229636885784694521

theorem tailTrace_40547 : CollatzResearch.WordTrace tailWord_40547 prefixEnd_40547 1542229636885784694521 := by
  unfold tailWord_40547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478870584112618721391895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 985913722741745814261263 1478870584112618721391895)
  ·
    refine ⟨2218305876168928082087843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1478870584112618721391895 2218305876168928082087843)
    ·
      refine ⟨3327458814253392123131765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218305876168928082087843 3327458814253392123131765)
      ·
        refine ⟨311949263836255511543603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3327458814253392123131765 311949263836255511543603)
        ·
          refine ⟨467923895754383267315405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311949263836255511543603 467923895754383267315405)
          ·
            refine ⟨175471460907893725243277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467923895754383267315405 175471460907893725243277)
            ·
              refine ⟨65801797840460146966229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175471460907893725243277 65801797840460146966229)
              ·
                refine ⟨1542229636885784694521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65801797840460146966229 1542229636885784694521)
                ·
                  rfl

theorem cell22_40547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 7].length) (baseStart_40547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40547 prefixEnd_40547 := by exact prefixLift 40547
  have htrace : WordTrace (prefixWord ++ tailWord_40547) baseStart_40547 baseEnd_40547 := by
    simpa [prefixWord, tailWord_40547, baseEnd_40547] using wordTrace_append hprefix tailTrace_40547
  have hstable : (prefixWord ++ tailWord_40547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40547).length < 2 ^ (prefixWord ++ tailWord_40547).sum := by decide
  have hdescent : baseEnd_40547 < baseStart_40547 := by decide
  rcases family_descends (prefixWord ++ tailWord_40547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40566 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_40566 : Nat := 118140960795 + 40566 * 2 ^ 59
def prefixEnd_40566 : Nat := 4983230072969 + 3 ^ 40 * 40566 * 2
def baseEnd_40566 : Nat := 13886570820262346025631

theorem tailTrace_40566 : CollatzResearch.WordTrace tailWord_40566 prefixEnd_40566 13886570820262346025631 := by
  unfold tailWord_40566
  simp only [CollatzResearch.WordTrace]
  refine ⟨92472723190236560395847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 986375714029189977555701 92472723190236560395847)
  ·
    refine ⟨138709084785354840593771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92472723190236560395847 138709084785354840593771)
    ·
      refine ⟨208063627178032260890657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138709084785354840593771 208063627178032260890657)
      ·
        refine ⟨156047720383524195667993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208063627178032260890657 156047720383524195667993)
        ·
          refine ⟨117035790287643146750995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156047720383524195667993 117035790287643146750995)
          ·
            refine ⟨175553685431464720126493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117035790287643146750995 175553685431464720126493)
            ·
              refine ⟨65832632036799270047435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175553685431464720126493 65832632036799270047435)
              ·
                refine ⟨98748948055198905071153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65832632036799270047435 98748948055198905071153)
                ·
                  refine ⟨74061711041399178803365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98748948055198905071153 74061711041399178803365)
                  ·
                    refine ⟨13886570820262346025631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74061711041399178803365 13886570820262346025631)
                    ·
                      rfl

theorem cell22_40566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_40566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40566 prefixEnd_40566 := by exact prefixLift 40566
  have htrace : WordTrace (prefixWord ++ tailWord_40566) baseStart_40566 baseEnd_40566 := by
    simpa [prefixWord, tailWord_40566, baseEnd_40566] using wordTrace_append hprefix tailTrace_40566
  have hstable : (prefixWord ++ tailWord_40566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40566).length < 2 ^ (prefixWord ++ tailWord_40566).sum := by decide
  have hdescent : baseEnd_40566 < baseStart_40566 := by decide
  rcases family_descends (prefixWord ++ tailWord_40566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40639 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 1, 4]
def baseStart_40639 : Nat := 118140960795 + 40639 * 2 ^ 59
def prefixEnd_40639 : Nat := 4983230072969 + 3 ^ 40 * 40639 * 2
def baseEnd_40639 : Nat := 13911560212114488950407

theorem tailTrace_40639 : CollatzResearch.WordTrace tailWord_40639 prefixEnd_40639 13911560212114488950407 := by
  unfold tailWord_40639
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482226099779318433740971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 988150733186212289160647 1482226099779318433740971)
  ·
    refine ⟨2223339149668977650611457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1482226099779318433740971 2223339149668977650611457)
    ·
      refine ⟨1667504362251733237958593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2223339149668977650611457 1667504362251733237958593)
      ·
        refine ⟨1250628271688799928468945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667504362251733237958593 1250628271688799928468945)
        ·
          refine ⟨937971203766599946351709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1250628271688799928468945 937971203766599946351709)
          ·
            refine ⟨351739201412474979881891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 937971203766599946351709 351739201412474979881891)
            ·
              refine ⟨527608802118712469822837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351739201412474979881891 527608802118712469822837)
              ·
                refine ⟨49463325198629294045891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 527608802118712469822837 49463325198629294045891)
                ·
                  refine ⟨74194987797943941068837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49463325198629294045891 74194987797943941068837)
                  ·
                    refine ⟨13911560212114488950407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74194987797943941068837 13911560212114488950407)
                    ·
                      rfl

theorem cell22_40639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_40639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40639 prefixEnd_40639 := by exact prefixLift 40639
  have htrace : WordTrace (prefixWord ++ tailWord_40639) baseStart_40639 baseEnd_40639 := by
    simpa [prefixWord, tailWord_40639, baseEnd_40639] using wordTrace_append hprefix tailTrace_40639
  have hstable : (prefixWord ++ tailWord_40639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40639).length < 2 ^ (prefixWord ++ tailWord_40639).sum := by decide
  have hdescent : baseEnd_40639 < baseStart_40639 := by decide
  rcases family_descends (prefixWord ++ tailWord_40639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40673 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_40673 : Nat := 118140960795 + 40673 * 2 ^ 59
def prefixEnd_40673 : Nat := 4983230072969 + 3 ^ 40 * 40673 * 2
def baseEnd_40673 : Nat := 13923199106949733600303

theorem tailTrace_40673 : CollatzResearch.WordTrace tailWord_40673 prefixEnd_40673 13923199106949733600303 := by
  unfold tailWord_40673
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483466181656142240478673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 988977454437428160319115 1483466181656142240478673)
  ·
    refine ⟨1112599636242106680359005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1483466181656142240478673 1112599636242106680359005)
    ·
      refine ⟨417224863590790005134627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1112599636242106680359005 417224863590790005134627)
      ·
        refine ⟨625837295386185007701941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417224863590790005134627 625837295386185007701941)
        ·
          refine ⟨58672246442454844472057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 625837295386185007701941 58672246442454844472057)
          ·
            refine ⟨44004184831841133354043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58672246442454844472057 44004184831841133354043)
            ·
              refine ⟨66006277247761700031065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44004184831841133354043 66006277247761700031065)
              ·
                refine ⟨49504707935821275023299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66006277247761700031065 49504707935821275023299)
                ·
                  refine ⟨74257061903731912534949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49504707935821275023299 74257061903731912534949)
                  ·
                    refine ⟨13923199106949733600303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74257061903731912534949 13923199106949733600303)
                    ·
                      rfl

theorem cell22_40673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_40673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40673 prefixEnd_40673 := by exact prefixLift 40673
  have htrace : WordTrace (prefixWord ++ tailWord_40673) baseStart_40673 baseEnd_40673 := by
    simpa [prefixWord, tailWord_40673, baseEnd_40673] using wordTrace_append hprefix tailTrace_40673
  have hstable : (prefixWord ++ tailWord_40673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40673).length < 2 ^ (prefixWord ++ tailWord_40673).sum := by decide
  have hdescent : baseEnd_40673 < baseStart_40673 := by decide
  rcases family_descends (prefixWord ++ tailWord_40673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40684 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_40684 : Nat := 118140960795 + 40684 * 2 ^ 59
def prefixEnd_40684 : Nat := 4983230072969 + 3 ^ 40 * 40684 * 2
def baseEnd_40684 : Nat := 13926964631749371575269

theorem tailTrace_40684 : CollatzResearch.WordTrace tailWord_40684 prefixEnd_40684 13926964631749371575269 := by
  unfold tailWord_40684
  simp only [CollatzResearch.WordTrace]
  refine ⟨741933692308145559564553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 989244923077527412752737 741933692308145559564553)
  ·
    refine ⟨556450269231109169673415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 741933692308145559564553 556450269231109169673415)
    ·
      refine ⟨834675403846663754510123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556450269231109169673415 834675403846663754510123)
      ·
        refine ⟨1252013105769995631765185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834675403846663754510123 1252013105769995631765185)
        ·
          refine ⟨939009829327496723823889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252013105769995631765185 939009829327496723823889)
          ·
            refine ⟨704257371995622542867917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939009829327496723823889 704257371995622542867917)
            ·
              refine ⟨264096514498358453575469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704257371995622542867917 264096514498358453575469)
              ·
                refine ⟨99036192936884420090801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264096514498358453575469 99036192936884420090801)
                ·
                  refine ⟨74277144702663315068101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99036192936884420090801 74277144702663315068101)
                  ·
                    refine ⟨13926964631749371575269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74277144702663315068101 13926964631749371575269)
                    ·
                      rfl

theorem cell22_40684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_40684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40684 prefixEnd_40684 := by exact prefixLift 40684
  have htrace : WordTrace (prefixWord ++ tailWord_40684) baseStart_40684 baseEnd_40684 := by
    simpa [prefixWord, tailWord_40684, baseEnd_40684] using wordTrace_append hprefix tailTrace_40684
  have hstable : (prefixWord ++ tailWord_40684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40684).length < 2 ^ (prefixWord ++ tailWord_40684).sum := by decide
  have hdescent : baseEnd_40684 < baseStart_40684 := by decide
  rcases family_descends (prefixWord ++ tailWord_40684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40748 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_40748 : Nat := 118140960795 + 40748 * 2 ^ 59
def prefixEnd_40748 : Nat := 4983230072969 + 3 ^ 40 * 40748 * 2
def baseEnd_40748 : Nat := 13948873139674537975073

theorem tailTrace_40748 : CollatzResearch.WordTrace tailWord_40748 prefixEnd_40748 13948873139674537975073 := by
  unfold tailWord_40748
  simp only [CollatzResearch.WordTrace]
  refine ⟨743100828192215024729449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 990801104256286699639265 743100828192215024729449)
  ·
    refine ⟨557325621144161268547087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 743100828192215024729449 557325621144161268547087)
    ·
      refine ⟨835988431716241902820631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557325621144161268547087 835988431716241902820631)
      ·
        refine ⟨1253982647574362854230947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835988431716241902820631 1253982647574362854230947)
        ·
          refine ⟨1880973971361544281346421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253982647574362854230947 1880973971361544281346421)
          ·
            refine ⟨176341309815144776376227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1880973971361544281346421 176341309815144776376227)
            ·
              refine ⟨264511964722717164564341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176341309815144776376227 264511964722717164564341)
              ·
                refine ⟨24797996692754734177907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264511964722717164564341 24797996692754734177907)
                ·
                  refine ⟨37196995039132101266861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24797996692754734177907 37196995039132101266861)
                  ·
                    refine ⟨13948873139674537975073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37196995039132101266861 13948873139674537975073)
                    ·
                      rfl

theorem cell22_40748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_40748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40748 prefixEnd_40748 := by exact prefixLift 40748
  have htrace : WordTrace (prefixWord ++ tailWord_40748) baseStart_40748 baseEnd_40748 := by
    simpa [prefixWord, tailWord_40748, baseEnd_40748] using wordTrace_append hprefix tailTrace_40748
  have hstable : (prefixWord ++ tailWord_40748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40748).length < 2 ^ (prefixWord ++ tailWord_40748).sum := by decide
  have hdescent : baseEnd_40748 < baseStart_40748 := by decide
  rcases family_descends (prefixWord ++ tailWord_40748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40765 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_40765 : Nat := 118140960795 + 40765 * 2 ^ 59
def prefixEnd_40765 : Nat := 4983230072969 + 3 ^ 40 * 40765 * 2
def baseEnd_40765 : Nat := 13954692587092160300021

theorem tailTrace_40765 : CollatzResearch.WordTrace tailWord_40765 prefixEnd_40765 13954692587092160300021 := by
  unfold tailWord_40765
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486821697322841952827749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 991214464881894635218499 1486821697322841952827749)
  ·
    refine ⟨278779068248032866155203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1486821697322841952827749 278779068248032866155203)
    ·
      refine ⟨418168602372049299232805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278779068248032866155203 418168602372049299232805)
      ·
        refine ⟨78406612944759243606151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418168602372049299232805 78406612944759243606151)
        ·
          refine ⟨117609919417138865409227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78406612944759243606151 117609919417138865409227)
          ·
            refine ⟨176414879125708298113841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117609919417138865409227 176414879125708298113841)
            ·
              refine ⟨132311159344281223585381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176414879125708298113841 132311159344281223585381)
              ·
                refine ⟨24808342377052729422259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132311159344281223585381 24808342377052729422259)
                ·
                  refine ⟨37212513565579094133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24808342377052729422259 37212513565579094133389)
                  ·
                    refine ⟨13954692587092160300021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37212513565579094133389 13954692587092160300021)
                    ·
                      rfl

theorem cell22_40765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_40765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40765 prefixEnd_40765 := by exact prefixLift 40765
  have htrace : WordTrace (prefixWord ++ tailWord_40765) baseStart_40765 baseEnd_40765 := by
    simpa [prefixWord, tailWord_40765, baseEnd_40765] using wordTrace_append hprefix tailTrace_40765
  have hstable : (prefixWord ++ tailWord_40765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40765).length < 2 ^ (prefixWord ++ tailWord_40765).sum := by decide
  have hdescent : baseEnd_40765 < baseStart_40765 := by decide
  rcases family_descends (prefixWord ++ tailWord_40765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40842 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_40842 : Nat := 118140960795 + 40842 * 2 ^ 59
def prefixEnd_40842 : Nat := 4983230072969 + 3 ^ 40 * 40842 * 2
def baseEnd_40842 : Nat := 13981051260689626124785

theorem tailTrace_40842 : CollatzResearch.WordTrace tailWord_40842 prefixEnd_40842 13981051260689626124785 := by
  unfold tailWord_40842
  simp only [CollatzResearch.WordTrace]
  refine ⟨372407529510971025845195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 993086745362589402253853 372407529510971025845195)
  ·
    refine ⟨558611294266456538767793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372407529510971025845195 558611294266456538767793)
    ·
      refine ⟨418958470699842404075845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 558611294266456538767793 418958470699842404075845)
      ·
        refine ⟨78554713256220450764221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418958470699842404075845 78554713256220450764221)
        ·
          refine ⟨29458017471082669036583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78554713256220450764221 29458017471082669036583)
          ·
            refine ⟨44187026206624003554875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29458017471082669036583 44187026206624003554875)
            ·
              refine ⟨66280539309936005332313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44187026206624003554875 66280539309936005332313)
              ·
                refine ⟨49710404482452003999235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66280539309936005332313 49710404482452003999235)
                ·
                  refine ⟨74565606723678005998853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49710404482452003999235 74565606723678005998853)
                  ·
                    refine ⟨13981051260689626124785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74565606723678005998853 13981051260689626124785)
                    ·
                      rfl

theorem cell22_40842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_40842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40842 prefixEnd_40842 := by exact prefixLift 40842
  have htrace : WordTrace (prefixWord ++ tailWord_40842) baseStart_40842 baseEnd_40842 := by
    simpa [prefixWord, tailWord_40842, baseEnd_40842] using wordTrace_append hprefix tailTrace_40842
  have hstable : (prefixWord ++ tailWord_40842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40842).length < 2 ^ (prefixWord ++ tailWord_40842).sum := by decide
  have hdescent : baseEnd_40842 < baseStart_40842 := by decide
  rcases family_descends (prefixWord ++ tailWord_40842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40849 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_40849 : Nat := 118140960795 + 40849 * 2 ^ 59
def prefixEnd_40849 : Nat := 4983230072969 + 3 ^ 40 * 40849 * 2
def baseEnd_40849 : Nat := 13983447503743941199763

theorem tailTrace_40849 : CollatzResearch.WordTrace tailWord_40849 prefixEnd_40849 13983447503743941199763 := by
  unfold tailWord_40849
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489885429018524298885601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 993256952679016199257067 1489885429018524298885601)
  ·
    refine ⟨1117414071763893224164201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1489885429018524298885601 1117414071763893224164201)
    ·
      refine ⟨838060553822919918123151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1117414071763893224164201 838060553822919918123151)
      ·
        refine ⟨1257090830734379877184727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838060553822919918123151 1257090830734379877184727)
        ·
          refine ⟨1885636246101569815777091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257090830734379877184727 1885636246101569815777091)
          ·
            refine ⟨2828454369152354723665637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885636246101569815777091 2828454369152354723665637)
            ·
              refine ⟨530335194216066510687307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2828454369152354723665637 530335194216066510687307)
              ·
                refine ⟨795502791324099766030961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530335194216066510687307 795502791324099766030961)
                ·
                  refine ⟨596627093493074824523221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 795502791324099766030961 596627093493074824523221)
                  ·
                    refine ⟨13983447503743941199763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 596627093493074824523221 13983447503743941199763)
                    ·
                      rfl

theorem cell22_40849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_40849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40849 prefixEnd_40849 := by exact prefixLift 40849
  have htrace : WordTrace (prefixWord ++ tailWord_40849) baseStart_40849 baseEnd_40849 := by
    simpa [prefixWord, tailWord_40849, baseEnd_40849] using wordTrace_append hprefix tailTrace_40849
  have hstable : (prefixWord ++ tailWord_40849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40849).length < 2 ^ (prefixWord ++ tailWord_40849).sum := by decide
  have hdescent : baseEnd_40849 < baseStart_40849 := by decide
  rcases family_descends (prefixWord ++ tailWord_40849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40881 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_40881 : Nat := 118140960795 + 40881 * 2 ^ 59
def prefixEnd_40881 : Nat := 4983230072969 + 3 ^ 40 * 40881 * 2
def baseEnd_40881 : Nat := 13994401757706524399665

theorem tailTrace_40881 : CollatzResearch.WordTrace tailWord_40881 prefixEnd_40881 13994401757706524399665 := by
  unfold tailWord_40881
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491052564902593764050497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 994035043268395842700331 1491052564902593764050497)
  ·
    refine ⟨1118289423676945323037873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1491052564902593764050497 1118289423676945323037873)
    ·
      refine ⟨838717067757708992278405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118289423676945323037873 838717067757708992278405)
      ·
        refine ⟨157259450204570436052201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 838717067757708992278405 157259450204570436052201)
        ·
          refine ⟨117944587653427827039151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157259450204570436052201 117944587653427827039151)
          ·
            refine ⟨176916881480141740558727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117944587653427827039151 176916881480141740558727)
            ·
              refine ⟨265375322220212610838091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176916881480141740558727 265375322220212610838091)
              ·
                refine ⟨398062983330318916257137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265375322220212610838091 398062983330318916257137)
                ·
                  refine ⟨298547237497739187192853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398062983330318916257137 298547237497739187192853)
                  ·
                    refine ⟨13994401757706524399665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 298547237497739187192853 13994401757706524399665)
                    ·
                      rfl

theorem cell22_40881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_40881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40881 prefixEnd_40881 := by exact prefixLift 40881
  have htrace : WordTrace (prefixWord ++ tailWord_40881) baseStart_40881 baseEnd_40881 := by
    simpa [prefixWord, tailWord_40881, baseEnd_40881] using wordTrace_append hprefix tailTrace_40881
  have hstable : (prefixWord ++ tailWord_40881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40881).length < 2 ^ (prefixWord ++ tailWord_40881).sum := by decide
  have hdescent : baseEnd_40881 < baseStart_40881 := by decide
  rcases family_descends (prefixWord ++ tailWord_40881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40896 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_40896 : Nat := 118140960795 + 40896 * 2 ^ 59
def prefixEnd_40896 : Nat := 4983230072969 + 3 ^ 40 * 40896 * 2
def baseEnd_40896 : Nat := 4666512188083828424873

theorem tailTrace_40896 : CollatzResearch.WordTrace tailWord_40896 prefixEnd_40896 4666512188083828424873 := by
  unfold tailWord_40896
  simp only [CollatzResearch.WordTrace]
  refine ⟨745799829924125662923271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 994399773232167550564361 745799829924125662923271)
  ·
    refine ⟨1118699744886188494384907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745799829924125662923271 1118699744886188494384907)
    ·
      refine ⟨1678049617329282741577361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118699744886188494384907 1678049617329282741577361)
      ·
        refine ⟨1258537212996962056183021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678049617329282741577361 1258537212996962056183021)
        ·
          refine ⟨471951454873860771068633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1258537212996962056183021 471951454873860771068633)
          ·
            refine ⟨353963591155395578301475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471951454873860771068633 353963591155395578301475)
            ·
              refine ⟨530945386733093367452213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353963591155395578301475 530945386733093367452213)
              ·
                refine ⟨49776130006227503198645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 530945386733093367452213 49776130006227503198645)
                ·
                  refine ⟨4666512188083828424873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49776130006227503198645 4666512188083828424873)
                  ·
                    rfl

theorem cell22_40896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_40896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40896 prefixEnd_40896 := by exact prefixLift 40896
  have htrace : WordTrace (prefixWord ++ tailWord_40896) baseStart_40896 baseEnd_40896 := by
    simpa [prefixWord, tailWord_40896, baseEnd_40896] using wordTrace_append hprefix tailTrace_40896
  have hstable : (prefixWord ++ tailWord_40896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40896).length < 2 ^ (prefixWord ++ tailWord_40896).sum := by decide
  have hdescent : baseEnd_40896 < baseStart_40896 := by decide
  rcases family_descends (prefixWord ++ tailWord_40896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40917 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_40917 : Nat := 118140960795 + 40917 * 2 ^ 59
def prefixEnd_40917 : Nat := 4983230072969 + 3 ^ 40 * 40917 * 2
def baseEnd_40917 : Nat := 14006725293414430499555

theorem tailTrace_40917 : CollatzResearch.WordTrace tailWord_40917 prefixEnd_40917 14006725293414430499555 := by
  unfold tailWord_40917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492365592772171912361005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 994910395181447941574003 1492365592772171912361005)
  ·
    refine ⟨559637097289564467135377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1492365592772171912361005 559637097289564467135377)
    ·
      refine ⟨419727822967173350351533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 559637097289564467135377 419727822967173350351533)
      ·
        refine ⟨157397933612690006381825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419727822967173350351533 157397933612690006381825)
        ·
          refine ⟨118048450209517504786369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157397933612690006381825 118048450209517504786369)
          ·
            refine ⟨88536337657138128589777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118048450209517504786369 88536337657138128589777)
            ·
              refine ⟨66402253242853596442333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88536337657138128589777 66402253242853596442333)
              ·
                refine ⟨24900844966070098665875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66402253242853596442333 24900844966070098665875)
                ·
                  refine ⟨37351267449105147998813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24900844966070098665875 37351267449105147998813)
                  ·
                    refine ⟨14006725293414430499555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37351267449105147998813 14006725293414430499555)
                    ·
                      rfl

theorem cell22_40917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_40917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40917 prefixEnd_40917 := by exact prefixLift 40917
  have htrace : WordTrace (prefixWord ++ tailWord_40917) baseStart_40917 baseEnd_40917 := by
    simpa [prefixWord, tailWord_40917, baseEnd_40917] using wordTrace_append hprefix tailTrace_40917
  have hstable : (prefixWord ++ tailWord_40917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40917).length < 2 ^ (prefixWord ++ tailWord_40917).sum := by decide
  have hdescent : baseEnd_40917 < baseStart_40917 := by decide
  rcases family_descends (prefixWord ++ tailWord_40917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40930 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_40930 : Nat := 118140960795 + 40930 * 2 ^ 59
def prefixEnd_40930 : Nat := 4983230072969 + 3 ^ 40 * 40930 * 2
def baseEnd_40930 : Nat := 4670391819695576641505

theorem tailTrace_40930 : CollatzResearch.WordTrace tailWord_40930 prefixEnd_40930 4670391819695576641505 := by
  unfold tailWord_40930
  simp only [CollatzResearch.WordTrace]
  refine ⟨373209935431268783146061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 995226494483383421722829 373209935431268783146061)
  ·
    refine ⟨139953725786725793679773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 373209935431268783146061 139953725786725793679773)
    ·
      refine ⟨52482647170022172629915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139953725786725793679773 52482647170022172629915)
      ·
        refine ⟨78723970755033258944873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52482647170022172629915 78723970755033258944873)
        ·
          refine ⟨59042978066274944208655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78723970755033258944873 59042978066274944208655)
          ·
            refine ⟨88564467099412416312983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59042978066274944208655 88564467099412416312983)
            ·
              refine ⟨132846700649118624469475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88564467099412416312983 132846700649118624469475)
              ·
                refine ⟨199270050973677936704213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132846700649118624469475 199270050973677936704213)
                ·
                  refine ⟨4670391819695576641505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 199270050973677936704213 4670391819695576641505)
                  ·
                    rfl

theorem cell22_40930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_40930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40930 prefixEnd_40930 := by exact prefixLift 40930
  have htrace : WordTrace (prefixWord ++ tailWord_40930) baseStart_40930 baseEnd_40930 := by
    simpa [prefixWord, tailWord_40930, baseEnd_40930] using wordTrace_append hprefix tailTrace_40930
  have hstable : (prefixWord ++ tailWord_40930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40930).length < 2 ^ (prefixWord ++ tailWord_40930).sum := by decide
  have hdescent : baseEnd_40930 < baseStart_40930 := by decide
  rcases family_descends (prefixWord ++ tailWord_40930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40971 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 6]
def baseStart_40971 : Nat := 118140960795 + 40971 * 2 ^ 59
def prefixEnd_40971 : Nat := 4983230072969 + 3 ^ 40 * 40971 * 2
def baseEnd_40971 : Nat := 14025210596976289649389

theorem tailTrace_40971 : CollatzResearch.WordTrace tailWord_40971 prefixEnd_40971 14025210596976289649389 := by
  unfold tailWord_40971
  simp only [CollatzResearch.WordTrace]
  refine ⟨1494335134576539134826767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 996223423051026089884511 1494335134576539134826767)
  ·
    refine ⟨2241502701864808702240151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1494335134576539134826767 2241502701864808702240151)
    ·
      refine ⟨3362254052797213053360227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2241502701864808702240151 3362254052797213053360227)
      ·
        refine ⟨5043381079195819580040341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3362254052797213053360227 5043381079195819580040341)
        ·
          refine ⟨236408488087304042814391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5043381079195819580040341 236408488087304042814391)
          ·
            refine ⟨354612732130956064221587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236408488087304042814391 354612732130956064221587)
            ·
              refine ⟨531919098196434096332381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354612732130956064221587 531919098196434096332381)
              ·
                refine ⟨199469661823662786124643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531919098196434096332381 199469661823662786124643)
                ·
                  refine ⟨299204492735494179186965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199469661823662786124643 299204492735494179186965)
                  ·
                    refine ⟨14025210596976289649389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 299204492735494179186965 14025210596976289649389)
                    ·
                      rfl

theorem cell22_40971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_40971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40971 prefixEnd_40971 := by exact prefixLift 40971
  have htrace : WordTrace (prefixWord ++ tailWord_40971) baseStart_40971 baseEnd_40971 := by
    simpa [prefixWord, tailWord_40971, baseEnd_40971] using wordTrace_append hprefix tailTrace_40971
  have hstable : (prefixWord ++ tailWord_40971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40971).length < 2 ^ (prefixWord ++ tailWord_40971).sum := by decide
  have hdescent : baseEnd_40971 < baseStart_40971 := by decide
  rcases family_descends (prefixWord ++ tailWord_40971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40986 : List Nat := [3, 1, 1, 3, 1, 3, 10]
def baseStart_40986 : Nat := 118140960795 + 40986 * 2 ^ 59
def prefixEnd_40986 : Nat := 4983230072969 + 3 ^ 40 * 40986 * 2
def baseEnd_40986 : Nat := 519642422352638908309

theorem tailTrace_40986 : CollatzResearch.WordTrace tailWord_40986 prefixEnd_40986 519642422352638908309 := by
  unfold tailWord_40986
  simp only [CollatzResearch.WordTrace]
  refine ⟨373720557380549174155703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 996588153014797797748541 373720557380549174155703)
  ·
    refine ⟨560580836070823761233555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373720557380549174155703 560580836070823761233555)
    ·
      refine ⟨840871254106235641850333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560580836070823761233555 840871254106235641850333)
      ·
        refine ⟨315326720289838365693875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 840871254106235641850333 315326720289838365693875)
        ·
          refine ⟨472990080434757548540813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315326720289838365693875 472990080434757548540813)
          ·
            refine ⟨177371280163034080702805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472990080434757548540813 177371280163034080702805)
            ·
              refine ⟨519642422352638908309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 177371280163034080702805 519642422352638908309)
              ·
                rfl

theorem cell22_40986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 10].length) (baseStart_40986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40986 prefixEnd_40986 := by exact prefixLift 40986
  have htrace : WordTrace (prefixWord ++ tailWord_40986) baseStart_40986 baseEnd_40986 := by
    simpa [prefixWord, tailWord_40986, baseEnd_40986] using wordTrace_append hprefix tailTrace_40986
  have hstable : (prefixWord ++ tailWord_40986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40986).length < 2 ^ (prefixWord ++ tailWord_40986).sum := by decide
  have hdescent : baseEnd_40986 < baseStart_40986 := by decide
  rcases family_descends (prefixWord ++ tailWord_40986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40988 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_40988 : Nat := 118140960795 + 40988 * 2 ^ 59
def prefixEnd_40988 : Nat := 4983230072969 + 3 ^ 40 * 40988 * 2
def baseEnd_40988 : Nat := 14031030044393911974337

theorem tailTrace_40988 : CollatzResearch.WordTrace tailWord_40988 prefixEnd_40988 14031030044393911974337 := by
  unfold tailWord_40988
  simp only [CollatzResearch.WordTrace]
  refine ⟨747477587757475519097809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 996636783676634025463745 747477587757475519097809)
  ·
    refine ⟨560608190818106639323357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 747477587757475519097809 560608190818106639323357)
    ·
      refine ⟨210228071556789989746259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 560608190818106639323357 210228071556789989746259)
      ·
        refine ⟨315342107335184984619389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210228071556789989746259 315342107335184984619389)
        ·
          refine ⟨118253290250694369232271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315342107335184984619389 118253290250694369232271)
          ·
            refine ⟨177379935376041553848407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118253290250694369232271 177379935376041553848407)
            ·
              refine ⟨266069903064062330772611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177379935376041553848407 266069903064062330772611)
              ·
                refine ⟨399104854596093496158917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266069903064062330772611 399104854596093496158917)
                ·
                  refine ⟨74832160236767530529797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399104854596093496158917 74832160236767530529797)
                  ·
                    refine ⟨14031030044393911974337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74832160236767530529797 14031030044393911974337)
                    ·
                      rfl

theorem cell22_40988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_40988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_40988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_40988 prefixEnd_40988 := by exact prefixLift 40988
  have htrace : WordTrace (prefixWord ++ tailWord_40988) baseStart_40988 baseEnd_40988 := by
    simpa [prefixWord, tailWord_40988, baseEnd_40988] using wordTrace_append hprefix tailTrace_40988
  have hstable : (prefixWord ++ tailWord_40988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40988).length < 2 ^ (prefixWord ++ tailWord_40988).sum := by decide
  have hdescent : baseEnd_40988 < baseStart_40988 := by decide
  rcases family_descends (prefixWord ++ tailWord_40988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41018 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_41018 : Nat := 118140960795 + 41018 * 2 ^ 59
def prefixEnd_41018 : Nat := 4983230072969 + 3 ^ 40 * 41018 * 2
def baseEnd_41018 : Nat := 14041299657483833724245

theorem tailTrace_41018 : CollatzResearch.WordTrace tailWord_41018 prefixEnd_41018 14041299657483833724245 := by
  unfold tailWord_41018
  simp only [CollatzResearch.WordTrace]
  refine ⟨374012341351566540446927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 997366243604177441191805 374012341351566540446927)
  ·
    refine ⟨561018512027349810670391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374012341351566540446927 561018512027349810670391)
    ·
      refine ⟨841527768041024716005587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561018512027349810670391 841527768041024716005587)
      ·
        refine ⟨1262291652061537074008381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841527768041024716005587 1262291652061537074008381)
        ·
          refine ⟨473359369523076402753143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1262291652061537074008381 473359369523076402753143)
          ·
            refine ⟨710039054284614604129715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473359369523076402753143 710039054284614604129715)
            ·
              refine ⟨1065058581426921906194573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710039054284614604129715 1065058581426921906194573)
              ·
                refine ⟨399396968035095714822965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1065058581426921906194573 399396968035095714822965)
                ·
                  refine ⟨37443465753290223264653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399396968035095714822965 37443465753290223264653)
                  ·
                    refine ⟨14041299657483833724245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37443465753290223264653 14041299657483833724245)
                    ·
                      rfl

theorem cell22_41018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_41018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41018 prefixEnd_41018 := by exact prefixLift 41018
  have htrace : WordTrace (prefixWord ++ tailWord_41018) baseStart_41018 baseEnd_41018 := by
    simpa [prefixWord, tailWord_41018, baseEnd_41018] using wordTrace_append hprefix tailTrace_41018
  have hstable : (prefixWord ++ tailWord_41018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41018).length < 2 ^ (prefixWord ++ tailWord_41018).sum := by decide
  have hdescent : baseEnd_41018 < baseStart_41018 := by decide
  rcases family_descends (prefixWord ++ tailWord_41018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41022 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_41022 : Nat := 118140960795 + 41022 * 2 ^ 59
def prefixEnd_41022 : Nat := 4983230072969 + 3 ^ 40 * 41022 * 2
def baseEnd_41022 : Nat := 14042668939229156624233

theorem tailTrace_41022 : CollatzResearch.WordTrace tailWord_41022 prefixEnd_41022 14042668939229156624233 := by
  unfold tailWord_41022
  simp only [CollatzResearch.WordTrace]
  refine ⟨187024407173971855616665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 997463504927849896622213 187024407173971855616665)
  ·
    refine ⟨140268305380478891712499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187024407173971855616665 140268305380478891712499)
    ·
      refine ⟨210402458070718337568749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140268305380478891712499 210402458070718337568749)
      ·
        refine ⟨78900921776519376588281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210402458070718337568749 78900921776519376588281)
        ·
          refine ⟨59175691332389532441211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78900921776519376588281 59175691332389532441211)
          ·
            refine ⟨88763536998584298661817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59175691332389532441211 88763536998584298661817)
            ·
              refine ⟨66572652748938223996363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88763536998584298661817 66572652748938223996363)
              ·
                refine ⟨99858979123407335994545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66572652748938223996363 99858979123407335994545)
                ·
                  refine ⟨74894234342555501995909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99858979123407335994545 74894234342555501995909)
                  ·
                    refine ⟨14042668939229156624233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74894234342555501995909 14042668939229156624233)
                    ·
                      rfl

theorem cell22_41022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_41022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41022 prefixEnd_41022 := by exact prefixLift 41022
  have htrace : WordTrace (prefixWord ++ tailWord_41022) baseStart_41022 baseEnd_41022 := by
    simpa [prefixWord, tailWord_41022, baseEnd_41022] using wordTrace_append hprefix tailTrace_41022
  have hstable : (prefixWord ++ tailWord_41022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41022).length < 2 ^ (prefixWord ++ tailWord_41022).sum := by decide
  have hdescent : baseEnd_41022 < baseStart_41022 := by decide
  rcases family_descends (prefixWord ++ tailWord_41022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41048 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_41048 : Nat := 118140960795 + 41048 * 2 ^ 59
def prefixEnd_41048 : Nat := 4983230072969 + 3 ^ 40 * 41048 * 2
def baseEnd_41048 : Nat := 4683856423524585158051

theorem tailTrace_41048 : CollatzResearch.WordTrace tailWord_41048 prefixEnd_41048 4683856423524585158051 := by
  unfold tailWord_41048
  simp only [CollatzResearch.WordTrace]
  refine ⟨748571777648790642689899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 998095703531720856919865 748571777648790642689899)
  ·
    refine ⟨1122857666473185964034849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748571777648790642689899 1122857666473185964034849)
    ·
      refine ⟨842143249854889473026137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1122857666473185964034849 842143249854889473026137)
      ·
        refine ⟨631607437391167104769603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 842143249854889473026137 631607437391167104769603)
        ·
          refine ⟨947411156086750657154405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631607437391167104769603 947411156086750657154405)
          ·
            refine ⟨177639591766265748216451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 947411156086750657154405 177639591766265748216451)
            ·
              refine ⟨266459387649398622324677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177639591766265748216451 266459387649398622324677)
              ·
                refine ⟨49961135184262241685877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266459387649398622324677 49961135184262241685877)
                ·
                  refine ⟨4683856423524585158051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49961135184262241685877 4683856423524585158051)
                  ·
                    rfl

theorem cell22_41048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_41048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41048 prefixEnd_41048 := by exact prefixLift 41048
  have htrace : WordTrace (prefixWord ++ tailWord_41048) baseStart_41048 baseEnd_41048 := by
    simpa [prefixWord, tailWord_41048, baseEnd_41048] using wordTrace_append hprefix tailTrace_41048
  have hstable : (prefixWord ++ tailWord_41048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41048).length < 2 ^ (prefixWord ++ tailWord_41048).sum := by decide
  have hdescent : baseEnd_41048 < baseStart_41048 := by decide
  rcases family_descends (prefixWord ++ tailWord_41048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41054 : List Nat := [4, 4, 1, 1, 2, 2, 1, 7]
def baseStart_41054 : Nat := 118140960795 + 41054 * 2 ^ 59
def prefixEnd_41054 : Nat := 4983230072969 + 3 ^ 40 * 41054 * 2
def baseEnd_41054 : Nat := 1561513688132415536015

theorem tailTrace_41054 : CollatzResearch.WordTrace tailWord_41054 prefixEnd_41054 1561513688132415536015 := by
  unfold tailWord_41054
  simp only [CollatzResearch.WordTrace]
  refine ⟨187170299159480538762277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 998241595517229540065477 187170299159480538762277)
  ·
    refine ⟨35094431092402601017927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187170299159480538762277 35094431092402601017927)
    ·
      refine ⟨52641646638603901526891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35094431092402601017927 52641646638603901526891)
      ·
        refine ⟨78962469957905852290337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52641646638603901526891 78962469957905852290337)
        ·
          refine ⟨59221852468429389217753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78962469957905852290337 59221852468429389217753)
          ·
            refine ⟨44416389351322041913315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59221852468429389217753 44416389351322041913315)
            ·
              refine ⟨66624584026983062869973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44416389351322041913315 66624584026983062869973)
              ·
                refine ⟨1561513688132415536015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66624584026983062869973 1561513688132415536015)
                ·
                  rfl

theorem cell22_41054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_41054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41054 prefixEnd_41054 := by exact prefixLift 41054
  have htrace : WordTrace (prefixWord ++ tailWord_41054) baseStart_41054 baseEnd_41054 := by
    simpa [prefixWord, tailWord_41054, baseEnd_41054] using wordTrace_append hprefix tailTrace_41054
  have hstable : (prefixWord ++ tailWord_41054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41054).length < 2 ^ (prefixWord ++ tailWord_41054).sum := by decide
  have hdescent : baseEnd_41054 < baseStart_41054 := by decide
  rcases family_descends (prefixWord ++ tailWord_41054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41063 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_41063 : Nat := 118140960795 + 41063 * 2 ^ 59
def prefixEnd_41063 : Nat := 4983230072969 + 3 ^ 40 * 41063 * 2
def baseEnd_41063 : Nat := 14056704077118716349107

theorem tailTrace_41063 : CollatzResearch.WordTrace tailWord_41063 prefixEnd_41063 14056704077118716349107 := by
  unfold tailWord_41063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497690650243238847175843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 998460433495492564783895 1497690650243238847175843)
  ·
    refine ⟨2246535975364858270763765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497690650243238847175843 2246535975364858270763765)
    ·
      refine ⟨210612747690455462884103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2246535975364858270763765 210612747690455462884103)
      ·
        refine ⟨315919121535683194326155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210612747690455462884103 315919121535683194326155)
        ·
          refine ⟨473878682303524791489233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315919121535683194326155 473878682303524791489233)
          ·
            refine ⟨355409011727643593616925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473878682303524791489233 355409011727643593616925)
            ·
              refine ⟨133278379397866347606347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355409011727643593616925 133278379397866347606347)
              ·
                refine ⟨199917569096799521409521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133278379397866347606347 199917569096799521409521)
                ·
                  refine ⟨149938176822599641057141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199917569096799521409521 149938176822599641057141)
                  ·
                    refine ⟨14056704077118716349107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149938176822599641057141 14056704077118716349107)
                    ·
                      rfl

theorem cell22_41063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_41063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41063 prefixEnd_41063 := by exact prefixLift 41063
  have htrace : WordTrace (prefixWord ++ tailWord_41063) baseStart_41063 baseEnd_41063 := by
    simpa [prefixWord, tailWord_41063, baseEnd_41063] using wordTrace_append hprefix tailTrace_41063
  have hstable : (prefixWord ++ tailWord_41063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41063).length < 2 ^ (prefixWord ++ tailWord_41063).sum := by decide
  have hdescent : baseEnd_41063 < baseStart_41063 := by decide
  rcases family_descends (prefixWord ++ tailWord_41063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41138 : List Nat := [3, 2, 1, 1, 1, 3, 3, 8]
def baseStart_41138 : Nat := 118140960795 + 41138 * 2 ^ 59
def prefixEnd_41138 : Nat := 4983230072969 + 3 ^ 40 * 41138 * 2
def baseEnd_41138 : Nat := 1564708678871502302653

theorem tailTrace_41138 : CollatzResearch.WordTrace tailWord_41138 prefixEnd_41138 1564708678871502302653 := by
  unfold tailWord_41138
  simp only [CollatzResearch.WordTrace]
  refine ⟨375106531242881664039017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1000284083314351104104045 375106531242881664039017)
  ·
    refine ⟨281329898432161248029263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 375106531242881664039017 281329898432161248029263)
    ·
      refine ⟨421994847648241872043895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281329898432161248029263 421994847648241872043895)
      ·
        refine ⟨632992271472362808065843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421994847648241872043895 632992271472362808065843)
        ·
          refine ⟨949488407208544212098765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632992271472362808065843 949488407208544212098765)
          ·
            refine ⟨356058152703204079537037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 949488407208544212098765 356058152703204079537037)
            ·
              refine ⟨133521807263701529826389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356058152703204079537037 133521807263701529826389)
              ·
                refine ⟨1564708678871502302653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 133521807263701529826389 1564708678871502302653)
                ·
                  rfl

theorem cell22_41138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_41138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41138 prefixEnd_41138 := by exact prefixLift 41138
  have htrace : WordTrace (prefixWord ++ tailWord_41138) baseStart_41138 baseEnd_41138 := by
    simpa [prefixWord, tailWord_41138, baseEnd_41138] using wordTrace_append hprefix tailTrace_41138
  have hstable : (prefixWord ++ tailWord_41138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41138).length < 2 ^ (prefixWord ++ tailWord_41138).sum := by decide
  have hdescent : baseEnd_41138 < baseStart_41138 := by decide
  rcases family_descends (prefixWord ++ tailWord_41138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41230 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_41230 : Nat := 118140960795 + 41230 * 2 ^ 59
def prefixEnd_41230 : Nat := 4983230072969 + 3 ^ 40 * 41230 * 2
def baseEnd_41230 : Nat := 14113871589985947423595

theorem tailTrace_41230 : CollatzResearch.WordTrace tailWord_41230 prefixEnd_41230 14113871589985947423595 := by
  unfold tailWord_41230
  simp only [CollatzResearch.WordTrace]
  refine ⟨187972705079778296063143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1002521093758817579003429 187972705079778296063143)
  ·
    refine ⟨281959057619667444094715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187972705079778296063143 281959057619667444094715)
    ·
      refine ⟨422938586429501166142073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281959057619667444094715 422938586429501166142073)
      ·
        refine ⟨317203939822125874606555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422938586429501166142073 317203939822125874606555)
        ·
          refine ⟨475805909733188811909833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317203939822125874606555 475805909733188811909833)
          ·
            refine ⟨356854432299891608932375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475805909733188811909833 356854432299891608932375)
            ·
              refine ⟨535281648449837413398563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356854432299891608932375 535281648449837413398563)
              ·
                refine ⟨802922472674756120097845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535281648449837413398563 802922472674756120097845)
                ·
                  refine ⟨75273981813258386259173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802922472674756120097845 75273981813258386259173)
                  ·
                    refine ⟨14113871589985947423595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75273981813258386259173 14113871589985947423595)
                    ·
                      rfl

theorem cell22_41230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_41230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41230 prefixEnd_41230 := by exact prefixLift 41230
  have htrace : WordTrace (prefixWord ++ tailWord_41230) baseStart_41230 baseEnd_41230 := by
    simpa [prefixWord, tailWord_41230, baseEnd_41230] using wordTrace_append hprefix tailTrace_41230
  have hstable : (prefixWord ++ tailWord_41230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41230).length < 2 ^ (prefixWord ++ tailWord_41230).sum := by decide
  have hdescent : baseEnd_41230 < baseStart_41230 := by decide
  rcases family_descends (prefixWord ++ tailWord_41230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41255 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 1, 3]
def baseStart_41255 : Nat := 118140960795 + 41255 * 2 ^ 59
def prefixEnd_41255 : Nat := 4983230072969 + 3 ^ 40 * 41255 * 2
def baseEnd_41255 : Nat := 14122429600894215548519

theorem tailTrace_41255 : CollatzResearch.WordTrace tailWord_41255 prefixEnd_41255 14122429600894215548519 := by
  unfold tailWord_41255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504693465547655638165219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1003128977031770425443479 1504693465547655638165219)
  ·
    refine ⟨2257040198321483457247829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504693465547655638165219 2257040198321483457247829)
    ·
      refine ⟨26449689824079884264623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 2257040198321483457247829 26449689824079884264623)
      ·
        refine ⟨39674534736119826396935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26449689824079884264623 39674534736119826396935)
        ·
          refine ⟨59511802104179739595403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39674534736119826396935 59511802104179739595403)
          ·
            refine ⟨89267703156269609393105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59511802104179739595403 89267703156269609393105)
            ·
              refine ⟨66950777367202207044829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89267703156269609393105 66950777367202207044829)
              ·
                refine ⟨25106541512700827641811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66950777367202207044829 25106541512700827641811)
                ·
                  refine ⟨37659812269051241462717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25106541512700827641811 37659812269051241462717)
                  ·
                    refine ⟨14122429600894215548519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37659812269051241462717 14122429600894215548519)
                    ·
                      rfl

theorem cell22_41255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_41255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41255 prefixEnd_41255 := by exact prefixLift 41255
  have htrace : WordTrace (prefixWord ++ tailWord_41255) baseStart_41255 baseEnd_41255 := by
    simpa [prefixWord, tailWord_41255, baseEnd_41255] using wordTrace_append hprefix tailTrace_41255
  have hstable : (prefixWord ++ tailWord_41255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41255).length < 2 ^ (prefixWord ++ tailWord_41255).sum := by decide
  have hdescent : baseEnd_41255 < baseStart_41255 := by decide
  rcases family_descends (prefixWord ++ tailWord_41255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41260 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_41260 : Nat := 118140960795 + 41260 * 2 ^ 59
def prefixEnd_41260 : Nat := 4983230072969 + 3 ^ 40 * 41260 * 2
def baseEnd_41260 : Nat := 14124141203075869173503

theorem tailTrace_41260 : CollatzResearch.WordTrace tailWord_41260 prefixEnd_41260 14124141203075869173503 := by
  unfold tailWord_41260
  simp only [CollatzResearch.WordTrace]
  refine ⟨752437915264770746048617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1003250553686360994731489 752437915264770746048617)
  ·
    refine ⟨564328436448578059536463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 752437915264770746048617 564328436448578059536463)
    ·
      refine ⟨846492654672867089304695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564328436448578059536463 846492654672867089304695)
      ·
        refine ⟨1269738982009300633957043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846492654672867089304695 1269738982009300633957043)
        ·
          refine ⟨1904608473013950950935565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269738982009300633957043 1904608473013950950935565)
          ·
            refine ⟨714228177380231606600837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1904608473013950950935565 714228177380231606600837)
            ·
              refine ⟨133917783258793426237657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 714228177380231606600837 133917783258793426237657)
              ·
                refine ⟨100438337444095069678243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133917783258793426237657 100438337444095069678243)
                ·
                  refine ⟨150657506166142604517365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100438337444095069678243 150657506166142604517365)
                  ·
                    refine ⟨14124141203075869173503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150657506166142604517365 14124141203075869173503)
                    ·
                      rfl

theorem cell22_41260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_41260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41260 prefixEnd_41260 := by exact prefixLift 41260
  have htrace : WordTrace (prefixWord ++ tailWord_41260) baseStart_41260 baseEnd_41260 := by
    simpa [prefixWord, tailWord_41260, baseEnd_41260] using wordTrace_append hprefix tailTrace_41260
  have hstable : (prefixWord ++ tailWord_41260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41260).length < 2 ^ (prefixWord ++ tailWord_41260).sum := by decide
  have hdescent : baseEnd_41260 < baseStart_41260 := by decide
  rcases family_descends (prefixWord ++ tailWord_41260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41339 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 3, 3]
def baseStart_41339 : Nat := 118140960795 + 41339 * 2 ^ 59
def prefixEnd_41339 : Nat := 4983230072969 + 3 ^ 40 * 41339 * 2
def baseEnd_41339 : Nat := 14151184517545996448261

theorem tailTrace_41339 : CollatzResearch.WordTrace tailWord_41339 prefixEnd_41339 14151184517545996448261 := by
  unfold tailWord_41339
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507757197243337984223071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1005171464828891989482047 1507757197243337984223071)
  ·
    refine ⟨2261635795865006976334607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507757197243337984223071 2261635795865006976334607)
    ·
      refine ⟨3392453693797510464501911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2261635795865006976334607 3392453693797510464501911)
      ·
        refine ⟨5088680540696265696752867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392453693797510464501911 5088680540696265696752867)
        ·
          refine ⟨7633020811044398545129301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5088680540696265696752867 7633020811044398545129301)
          ·
            refine ⟨44724731314713272725367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 7633020811044398545129301 44724731314713272725367)
            ·
              refine ⟨67087096972069909088051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44724731314713272725367 67087096972069909088051)
              ·
                refine ⟨100630645458104863632077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67087096972069909088051 100630645458104863632077)
                ·
                  refine ⟨37736492046789323862029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100630645458104863632077 37736492046789323862029)
                  ·
                    refine ⟨14151184517545996448261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37736492046789323862029 14151184517545996448261)
                    ·
                      rfl

theorem cell22_41339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3].length) (baseStart_41339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41339 prefixEnd_41339 := by exact prefixLift 41339
  have htrace : WordTrace (prefixWord ++ tailWord_41339) baseStart_41339 baseEnd_41339 := by
    simpa [prefixWord, tailWord_41339, baseEnd_41339] using wordTrace_append hprefix tailTrace_41339
  have hstable : (prefixWord ++ tailWord_41339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41339).length < 2 ^ (prefixWord ++ tailWord_41339).sum := by decide
  have hdescent : baseEnd_41339 < baseStart_41339 := by decide
  rcases family_descends (prefixWord ++ tailWord_41339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41352 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_41352 : Nat := 118140960795 + 41352 * 2 ^ 59
def prefixEnd_41352 : Nat := 4983230072969 + 3 ^ 40 * 41352 * 2
def baseEnd_41352 : Nat := 4718544894406098624407

theorem tailTrace_41352 : CollatzResearch.WordTrace tailWord_41352 prefixEnd_41352 4718544894406098624407 := by
  unfold tailWord_41352
  simp only [CollatzResearch.WordTrace]
  refine ⟨754115673098120602223155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1005487564130827469630873 754115673098120602223155)
  ·
    refine ⟨1131173509647180903334733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754115673098120602223155 1131173509647180903334733)
    ·
      refine ⟨424190066117692838750525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1131173509647180903334733 424190066117692838750525)
      ·
        refine ⟨159071274794134814531447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424190066117692838750525 159071274794134814531447)
        ·
          refine ⟨238606912191202221797171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159071274794134814531447 238606912191202221797171)
          ·
            refine ⟨357910368286803332695757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238606912191202221797171 357910368286803332695757)
            ·
              refine ⟨134216388107551249760909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357910368286803332695757 134216388107551249760909)
              ·
                refine ⟨50331145540331718660341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134216388107551249760909 50331145540331718660341)
                ·
                  refine ⟨4718544894406098624407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50331145540331718660341 4718544894406098624407)
                  ·
                    rfl

theorem cell22_41352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_41352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41352 prefixEnd_41352 := by exact prefixLift 41352
  have htrace : WordTrace (prefixWord ++ tailWord_41352) baseStart_41352 baseEnd_41352 := by
    simpa [prefixWord, tailWord_41352, baseEnd_41352] using wordTrace_append hprefix tailTrace_41352
  have hstable : (prefixWord ++ tailWord_41352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41352).length < 2 ^ (prefixWord ++ tailWord_41352).sum := by decide
  have hdescent : baseEnd_41352 < baseStart_41352 := by decide
  rcases family_descends (prefixWord ++ tailWord_41352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41425 : List Nat := [1, 2, 2, 1, 2, 1, 1, 12]
def baseStart_41425 : Nat := 118140960795 + 41425 * 2 ^ 59
def prefixEnd_41425 : Nat := 4983230072969 + 3 ^ 40 * 41425 * 2
def baseEnd_41425 : Nat := 1575624897230048755333

theorem tailTrace_41425 : CollatzResearch.WordTrace tailWord_41425 prefixEnd_41425 1575624897230048755333 := by
  unfold tailWord_41425
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510893874931774671853729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1007262583287849781235819 1510893874931774671853729)
  ·
    refine ⟨1133170406198831003890297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1510893874931774671853729 1133170406198831003890297)
    ·
      refine ⟨849877804649123252917723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1133170406198831003890297 849877804649123252917723)
      ·
        refine ⟨1274816706973684879376585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849877804649123252917723 1274816706973684879376585)
        ·
          refine ⟨956112530230263659532439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274816706973684879376585 956112530230263659532439)
          ·
            refine ⟨1434168795345395489298659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956112530230263659532439 1434168795345395489298659)
            ·
              refine ⟨2151253193018093233947989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434168795345395489298659 2151253193018093233947989)
              ·
                refine ⟨1575624897230048755333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 2151253193018093233947989 1575624897230048755333)
                ·
                  rfl

theorem cell22_41425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 12].length) (baseStart_41425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41425 prefixEnd_41425 := by exact prefixLift 41425
  have htrace : WordTrace (prefixWord ++ tailWord_41425) baseStart_41425 baseEnd_41425 := by
    simpa [prefixWord, tailWord_41425, baseEnd_41425] using wordTrace_append hprefix tailTrace_41425
  have hstable : (prefixWord ++ tailWord_41425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41425).length < 2 ^ (prefixWord ++ tailWord_41425).sum := by decide
  have hdescent : baseEnd_41425 < baseStart_41425 := by decide
  rcases family_descends (prefixWord ++ tailWord_41425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41476 : List Nat := [2, 3, 2, 3, 1, 3, 2, 6]
def baseStart_41476 : Nat := 118140960795 + 41476 * 2 ^ 59
def prefixEnd_41476 : Nat := 4983230072969 + 3 ^ 40 * 41476 * 2
def baseEnd_41476 : Nat := 1577564713035922863649

theorem tailTrace_41476 : CollatzResearch.WordTrace tailWord_41476 prefixEnd_41476 1577564713035922863649 := by
  unfold tailWord_41476
  simp only [CollatzResearch.WordTrace]
  refine ⟨756376998873505190980141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1008502665164673587973521 756376998873505190980141)
  ·
    refine ⟨283641374577564446617553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 756376998873505190980141 283641374577564446617553)
    ·
      refine ⟨212731030933173334963165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283641374577564446617553 212731030933173334963165)
      ·
        refine ⟨79774136599940000611187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212731030933173334963165 79774136599940000611187)
        ·
          refine ⟨119661204899910000916781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79774136599940000611187 119661204899910000916781)
          ·
            refine ⟨44872951837466250343793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119661204899910000916781 44872951837466250343793)
            ·
              refine ⟨33654713878099687757845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44872951837466250343793 33654713878099687757845)
              ·
                refine ⟨1577564713035922863649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33654713878099687757845 1577564713035922863649)
                ·
                  rfl

theorem cell22_41476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_41476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41476 prefixEnd_41476 := by exact prefixLift 41476
  have htrace : WordTrace (prefixWord ++ tailWord_41476) baseStart_41476 baseEnd_41476 := by
    simpa [prefixWord, tailWord_41476, baseEnd_41476] using wordTrace_append hprefix tailTrace_41476
  have hstable : (prefixWord ++ tailWord_41476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41476).length < 2 ^ (prefixWord ++ tailWord_41476).sum := by decide
  have hdescent : baseEnd_41476 < baseStart_41476 := by decide
  rcases family_descends (prefixWord ++ tailWord_41476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41478 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_41478 : Nat := 118140960795 + 41478 * 2 ^ 59
def prefixEnd_41478 : Nat := 4983230072969 + 3 ^ 40 * 41478 * 2
def baseEnd_41478 : Nat := 14198767058195967222835

theorem tailTrace_41478 : CollatzResearch.WordTrace tailWord_41478 prefixEnd_41478 14198767058195967222835 := by
  unfold tailWord_41478
  simp only [CollatzResearch.WordTrace]
  refine ⟨47275841991867647610409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1008551295826509815688725 47275841991867647610409)
  ·
    refine ⟨35456881493900735707807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47275841991867647610409 35456881493900735707807)
    ·
      refine ⟨53185322240851103561711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35456881493900735707807 53185322240851103561711)
      ·
        refine ⟨79777983361276655342567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53185322240851103561711 79777983361276655342567)
        ·
          refine ⟨119666975041914983013851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79777983361276655342567 119666975041914983013851)
          ·
            refine ⟨179500462562872474520777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119666975041914983013851 179500462562872474520777)
            ·
              refine ⟨134625346922154355890583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179500462562872474520777 134625346922154355890583)
              ·
                refine ⟨201938020383231533835875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134625346922154355890583 201938020383231533835875)
                ·
                  refine ⟨302907030574847300753813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201938020383231533835875 302907030574847300753813)
                  ·
                    refine ⟨14198767058195967222835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 302907030574847300753813 14198767058195967222835)
                    ·
                      rfl

theorem cell22_41478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_41478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41478 prefixEnd_41478 := by exact prefixLift 41478
  have htrace : WordTrace (prefixWord ++ tailWord_41478) baseStart_41478 baseEnd_41478 := by
    simpa [prefixWord, tailWord_41478, baseEnd_41478] using wordTrace_append hprefix tailTrace_41478
  have hstable : (prefixWord ++ tailWord_41478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41478).length < 2 ^ (prefixWord ++ tailWord_41478).sum := by decide
  have hdescent : baseEnd_41478 < baseStart_41478 := by decide
  rcases family_descends (prefixWord ++ tailWord_41478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41547 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_41547 : Nat := 118140960795 + 41547 * 2 ^ 59
def prefixEnd_41547 : Nat := 4983230072969 + 3 ^ 40 * 41547 * 2
def baseEnd_41547 : Nat := 14222387168302787247623

theorem tailTrace_41547 : CollatzResearch.WordTrace tailWord_41547 prefixEnd_41547 14222387168302787247623 := by
  unfold tailWord_41547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515343580489789507794895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1010229053659859671863263 1515343580489789507794895)
  ·
    refine ⟨2273015370734684261692343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1515343580489789507794895 2273015370734684261692343)
    ·
      refine ⟨3409523056102026392538515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2273015370734684261692343 3409523056102026392538515)
      ·
        refine ⟨5114284584153039588807773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409523056102026392538515 5114284584153039588807773)
        ·
          refine ⟨1917856719057389845802915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5114284584153039588807773 1917856719057389845802915)
          ·
            refine ⟨2876785078586084768704373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917856719057389845802915 2876785078586084768704373)
            ·
              refine ⟨269698601117445447066035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2876785078586084768704373 269698601117445447066035)
              ·
                refine ⟨404547901676168170599053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269698601117445447066035 404547901676168170599053)
                ·
                  refine ⟨151705463128563063974645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404547901676168170599053 151705463128563063974645)
                  ·
                    refine ⟨14222387168302787247623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151705463128563063974645 14222387168302787247623)
                    ·
                      rfl

theorem cell22_41547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_41547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41547 prefixEnd_41547 := by exact prefixLift 41547
  have htrace : WordTrace (prefixWord ++ tailWord_41547) baseStart_41547 baseEnd_41547 := by
    simpa [prefixWord, tailWord_41547, baseEnd_41547] using wordTrace_append hprefix tailTrace_41547
  have hstable : (prefixWord ++ tailWord_41547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41547).length < 2 ^ (prefixWord ++ tailWord_41547).sum := by decide
  have hdescent : baseEnd_41547 < baseStart_41547 := by decide
  rcases family_descends (prefixWord ++ tailWord_41547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41562 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_41562 : Nat := 118140960795 + 41562 * 2 ^ 59
def prefixEnd_41562 : Nat := 4983230072969 + 3 ^ 40 * 41562 * 2
def baseEnd_41562 : Nat := 14227521974847748122577

theorem tailTrace_41562 : CollatzResearch.WordTrace tailWord_41562 prefixEnd_41562 14227521974847748122577 := by
  unfold tailWord_41562
  simp only [CollatzResearch.WordTrace]
  refine ⟨378972668858861767397735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1010593783623631379727293 378972668858861767397735)
  ·
    refine ⟨568459003288292651096603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378972668858861767397735 568459003288292651096603)
    ·
      refine ⟨852688504932438976644905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568459003288292651096603 852688504932438976644905)
      ·
        refine ⟨639516378699329232483679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852688504932438976644905 639516378699329232483679)
        ·
          refine ⟨959274568048993848725519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639516378699329232483679 959274568048993848725519)
          ·
            refine ⟨1438911852073490773088279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959274568048993848725519 1438911852073490773088279)
            ·
              refine ⟨2158367778110236159632419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438911852073490773088279 2158367778110236159632419)
              ·
                refine ⟨3237551667165354239448629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158367778110236159632419 3237551667165354239448629)
                ·
                  refine ⟨303520468796751959948309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237551667165354239448629 303520468796751959948309)
                  ·
                    refine ⟨14227521974847748122577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 303520468796751959948309 14227521974847748122577)
                    ·
                      rfl

theorem cell22_41562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_41562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41562 prefixEnd_41562 := by exact prefixLift 41562
  have htrace : WordTrace (prefixWord ++ tailWord_41562) baseStart_41562 baseEnd_41562 := by
    simpa [prefixWord, tailWord_41562, baseEnd_41562] using wordTrace_append hprefix tailTrace_41562
  have hstable : (prefixWord ++ tailWord_41562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41562).length < 2 ^ (prefixWord ++ tailWord_41562).sum := by decide
  have hdescent : baseEnd_41562 < baseStart_41562 := by decide
  rcases family_descends (prefixWord ++ tailWord_41562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41581 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_41581 : Nat := 118140960795 + 41581 * 2 ^ 59
def prefixEnd_41581 : Nat := 4983230072969 + 3 ^ 40 * 41581 * 2
def baseEnd_41581 : Nat := 14234026063138031897519

theorem tailTrace_41581 : CollatzResearch.WordTrace tailWord_41581 prefixEnd_41581 14234026063138031897519 := by
  unfold tailWord_41581
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516583662366613314532597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1011055774911075543021731 1516583662366613314532597)
  ·
    refine ⟨142179718346869998237431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1516583662366613314532597 142179718346869998237431)
    ·
      refine ⟨213269577520304997356147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142179718346869998237431 213269577520304997356147)
      ·
        refine ⟨319904366280457496034221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213269577520304997356147 319904366280457496034221)
        ·
          refine ⟨119964137355171561012833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319904366280457496034221 119964137355171561012833)
          ·
            refine ⟨89973103016378670759625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119964137355171561012833 89973103016378670759625)
            ·
              refine ⟨67479827262284003069719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89973103016378670759625 67479827262284003069719)
              ·
                refine ⟨101219740893426004604579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67479827262284003069719 101219740893426004604579)
                ·
                  refine ⟨151829611340139006906869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101219740893426004604579 151829611340139006906869)
                  ·
                    refine ⟨14234026063138031897519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151829611340139006906869 14234026063138031897519)
                    ·
                      rfl

theorem cell22_41581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_41581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41581 prefixEnd_41581 := by exact prefixLift 41581
  have htrace : WordTrace (prefixWord ++ tailWord_41581) baseStart_41581 baseEnd_41581 := by
    simpa [prefixWord, tailWord_41581, baseEnd_41581] using wordTrace_append hprefix tailTrace_41581
  have hstable : (prefixWord ++ tailWord_41581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41581).length < 2 ^ (prefixWord ++ tailWord_41581).sum := by decide
  have hdescent : baseEnd_41581 < baseStart_41581 := by decide
  rcases family_descends (prefixWord ++ tailWord_41581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41592 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_41592 : Nat := 118140960795 + 41592 * 2 ^ 59
def prefixEnd_41592 : Nat := 4983230072969 + 3 ^ 40 * 41592 * 2
def baseEnd_41592 : Nat := 14237791587937669872485

theorem tailTrace_41592 : CollatzResearch.WordTrace tailWord_41592 prefixEnd_41592 14237791587937669872485 := by
  unfold tailWord_41592
  simp only [CollatzResearch.WordTrace]
  refine ⟨758492432663381096591515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1011323243551174795455353 758492432663381096591515)
  ·
    refine ⟨1137738648995071644887273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758492432663381096591515 1137738648995071644887273)
    ·
      refine ⟨853303986746303733665455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1137738648995071644887273 853303986746303733665455)
      ·
        refine ⟨1279955980119455600498183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853303986746303733665455 1279955980119455600498183)
        ·
          refine ⟨1919933970179183400747275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279955980119455600498183 1919933970179183400747275)
          ·
            refine ⟨2879900955268775101120913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919933970179183400747275 2879900955268775101120913)
            ·
              refine ⟨2159925716451581325840685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879900955268775101120913 2159925716451581325840685)
              ·
                refine ⟨809972143669342997190257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2159925716451581325840685 809972143669342997190257)
                ·
                  refine ⟨607479107752007247892693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809972143669342997190257 607479107752007247892693)
                  ·
                    refine ⟨14237791587937669872485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 607479107752007247892693 14237791587937669872485)
                    ·
                      rfl

theorem cell22_41592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_41592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41592 prefixEnd_41592 := by exact prefixLift 41592
  have htrace : WordTrace (prefixWord ++ tailWord_41592) baseStart_41592 baseEnd_41592 := by
    simpa [prefixWord, tailWord_41592, baseEnd_41592] using wordTrace_append hprefix tailTrace_41592
  have hstable : (prefixWord ++ tailWord_41592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41592).length < 2 ^ (prefixWord ++ tailWord_41592).sum := by decide
  have hdescent : baseEnd_41592 < baseStart_41592 := by decide
  rcases family_descends (prefixWord ++ tailWord_41592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41602 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_41602 : Nat := 118140960795 + 41602 * 2 ^ 59
def prefixEnd_41602 : Nat := 4983230072969 + 3 ^ 40 * 41602 * 2
def baseEnd_41602 : Nat := 14241214792300977122455

theorem tailTrace_41602 : CollatzResearch.WordTrace tailWord_41602 prefixEnd_41602 14241214792300977122455 := by
  unfold tailWord_41602
  simp only [CollatzResearch.WordTrace]
  refine ⟨379337398822633475261765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1011566396860355934031373 379337398822633475261765)
  ·
    refine ⟨71125762279243776611581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 379337398822633475261765 71125762279243776611581)
    ·
      refine ⟨26672160854716416229343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71125762279243776611581 26672160854716416229343)
      ·
        refine ⟨40008241282074624344015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26672160854716416229343 40008241282074624344015)
        ·
          refine ⟨60012361923111936516023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40008241282074624344015 60012361923111936516023)
          ·
            refine ⟨90018542884667904774035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60012361923111936516023 90018542884667904774035)
            ·
              refine ⟨135027814327001857161053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90018542884667904774035 135027814327001857161053)
              ·
                refine ⟨50635430372625696435395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135027814327001857161053 50635430372625696435395)
                ·
                  refine ⟨75953145558938544653093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50635430372625696435395 75953145558938544653093)
                  ·
                    refine ⟨14241214792300977122455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75953145558938544653093 14241214792300977122455)
                    ·
                      rfl

theorem cell22_41602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_41602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41602 prefixEnd_41602 := by exact prefixLift 41602
  have htrace : WordTrace (prefixWord ++ tailWord_41602) baseStart_41602 baseEnd_41602 := by
    simpa [prefixWord, tailWord_41602, baseEnd_41602] using wordTrace_append hprefix tailTrace_41602
  have hstable : (prefixWord ++ tailWord_41602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41602).length < 2 ^ (prefixWord ++ tailWord_41602).sum := by decide
  have hdescent : baseEnd_41602 < baseStart_41602 := by decide
  rcases family_descends (prefixWord ++ tailWord_41602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41609 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_41609 : Nat := 118140960795 + 41609 * 2 ^ 59
def prefixEnd_41609 : Nat := 4983230072969 + 3 ^ 40 * 41609 * 2
def baseEnd_41609 : Nat := 14243611035355292197433

theorem tailTrace_41609 : CollatzResearch.WordTrace tailWord_41609 prefixEnd_41609 14243611035355292197433 := by
  unfold tailWord_41609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517604906265174096551881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1011736604176782731034587 1517604906265174096551881)
  ·
    refine ⟨1138203679698880572413911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1517604906265174096551881 1138203679698880572413911)
    ·
      refine ⟨1707305519548320858620867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138203679698880572413911 1707305519548320858620867)
      ·
        refine ⟨2560958279322481287931301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707305519548320858620867 2560958279322481287931301)
        ·
          refine ⟨480179677372965241487119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2560958279322481287931301 480179677372965241487119)
          ·
            refine ⟨720269516059447862230679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480179677372965241487119 720269516059447862230679)
            ·
              refine ⟨1080404274089171793346019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720269516059447862230679 1080404274089171793346019)
              ·
                refine ⟨1620606411133757690019029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080404274089171793346019 1620606411133757690019029)
                ·
                  refine ⟨37982962760947445859821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1620606411133757690019029 37982962760947445859821)
                  ·
                    refine ⟨14243611035355292197433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37982962760947445859821 14243611035355292197433)
                    ·
                      rfl

theorem cell22_41609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_41609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41609 prefixEnd_41609 := by exact prefixLift 41609
  have htrace : WordTrace (prefixWord ++ tailWord_41609) baseStart_41609 baseEnd_41609 := by
    simpa [prefixWord, tailWord_41609, baseEnd_41609] using wordTrace_append hprefix tailTrace_41609
  have hstable : (prefixWord ++ tailWord_41609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41609).length < 2 ^ (prefixWord ++ tailWord_41609).sum := by decide
  have hdescent : baseEnd_41609 < baseStart_41609 := by decide
  rcases family_descends (prefixWord ++ tailWord_41609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41677 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_41677 : Nat := 118140960795 + 41677 * 2 ^ 59
def prefixEnd_41677 : Nat := 4983230072969 + 3 ^ 40 * 41677 * 2
def baseEnd_41677 : Nat := 14266888825025781497225

theorem tailTrace_41677 : CollatzResearch.WordTrace tailWord_41677 prefixEnd_41677 14266888825025781497225 := by
  unfold tailWord_41677
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520085070018821710027285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1013390046679214473351523 1520085070018821710027285)
  ·
    refine ⟨71253987657132267657529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1520085070018821710027285 71253987657132267657529)
    ·
      refine ⟨53440490742849200743147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71253987657132267657529 53440490742849200743147)
      ·
        refine ⟨80160736114273801114721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53440490742849200743147 80160736114273801114721)
        ·
          refine ⟨60120552085705350836041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80160736114273801114721 60120552085705350836041)
          ·
            refine ⟨45090414064279013127031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60120552085705350836041 45090414064279013127031)
            ·
              refine ⟨67635621096418519690547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45090414064279013127031 67635621096418519690547)
              ·
                refine ⟨101453431644627779535821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67635621096418519690547 101453431644627779535821)
                ·
                  refine ⟨38045036866735417325933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101453431644627779535821 38045036866735417325933)
                  ·
                    refine ⟨14266888825025781497225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38045036866735417325933 14266888825025781497225)
                    ·
                      rfl

theorem cell22_41677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_41677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41677 prefixEnd_41677 := by exact prefixLift 41677
  have htrace : WordTrace (prefixWord ++ tailWord_41677) baseStart_41677 baseEnd_41677 := by
    simpa [prefixWord, tailWord_41677, baseEnd_41677] using wordTrace_append hprefix tailTrace_41677
  have hstable : (prefixWord ++ tailWord_41677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41677).length < 2 ^ (prefixWord ++ tailWord_41677).sum := by decide
  have hdescent : baseEnd_41677 < baseStart_41677 := by decide
  rcases family_descends (prefixWord ++ tailWord_41677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41718 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_41718 : Nat := 118140960795 + 41718 * 2 ^ 59
def prefixEnd_41718 : Nat := 4983230072969 + 3 ^ 40 * 41718 * 2
def baseEnd_41718 : Nat := 4760307987638447074033

theorem tailTrace_41718 : CollatzResearch.WordTrace tailWord_41718 prefixEnd_41718 4760307987638447074033 := by
  unfold tailWord_41718
  simp only [CollatzResearch.WordTrace]
  refine ⟨95098778929392857016863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1014386975246857141513205 95098778929392857016863)
  ·
    refine ⟨142648168394089285525295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95098778929392857016863 142648168394089285525295)
    ·
      refine ⟨213972252591133928287943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142648168394089285525295 213972252591133928287943)
      ·
        refine ⟨320958378886700892431915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213972252591133928287943 320958378886700892431915)
        ·
          refine ⟨481437568330051338647873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320958378886700892431915 481437568330051338647873)
          ·
            refine ⟨361078176247538503985905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481437568330051338647873 361078176247538503985905)
            ·
              refine ⟨270808632185653877989429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361078176247538503985905 270808632185653877989429)
              ·
                refine ⟨25388309267405051061509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270808632185653877989429 25388309267405051061509)
                ·
                  refine ⟨4760307987638447074033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25388309267405051061509 4760307987638447074033)
                  ·
                    rfl

theorem cell22_41718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_41718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41718 prefixEnd_41718 := by exact prefixLift 41718
  have htrace : WordTrace (prefixWord ++ tailWord_41718) baseStart_41718 baseEnd_41718 := by
    simpa [prefixWord, tailWord_41718, baseEnd_41718] using wordTrace_append hprefix tailTrace_41718
  have hstable : (prefixWord ++ tailWord_41718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41718).length < 2 ^ (prefixWord ++ tailWord_41718).sum := by decide
  have hdescent : baseEnd_41718 < baseStart_41718 := by decide
  rcases family_descends (prefixWord ++ tailWord_41718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41735 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 4]
def baseStart_41735 : Nat := 118140960795 + 41735 * 2 ^ 59
def prefixEnd_41735 : Nat := 4983230072969 + 3 ^ 40 * 41735 * 2
def baseEnd_41735 : Nat := 4762247803444321182349

theorem tailTrace_41735 : CollatzResearch.WordTrace tailWord_41735 prefixEnd_41735 4762247803444321182349 := by
  unfold tailWord_41735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522200503808697615638659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1014800335872465077092439 1522200503808697615638659)
  ·
    refine ⟨2283300755713046423457989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522200503808697615638659 2283300755713046423457989)
    ·
      refine ⟨428118891696196204398373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2283300755713046423457989 428118891696196204398373)
      ·
        refine ⟨80272292193036788324695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428118891696196204398373 80272292193036788324695)
        ·
          refine ⟨120408438289555182487043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80272292193036788324695 120408438289555182487043)
          ·
            refine ⟨180612657434332773730565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120408438289555182487043 180612657434332773730565)
            ·
              refine ⟨33864873268937395074481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180612657434332773730565 33864873268937395074481)
              ·
                refine ⟨25398654951703046305861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33864873268937395074481 25398654951703046305861)
                ·
                  refine ⟨4762247803444321182349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25398654951703046305861 4762247803444321182349)
                  ·
                    rfl

theorem cell22_41735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 4].length) (baseStart_41735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41735 prefixEnd_41735 := by exact prefixLift 41735
  have htrace : WordTrace (prefixWord ++ tailWord_41735) baseStart_41735 baseEnd_41735 := by
    simpa [prefixWord, tailWord_41735, baseEnd_41735] using wordTrace_append hprefix tailTrace_41735
  have hstable : (prefixWord ++ tailWord_41735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41735).length < 2 ^ (prefixWord ++ tailWord_41735).sum := by decide
  have hdescent : baseEnd_41735 < baseStart_41735 := by decide
  rcases family_descends (prefixWord ++ tailWord_41735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41791 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 7]
def baseStart_41791 : Nat := 118140960795 + 41791 * 2 ^ 59
def prefixEnd_41791 : Nat := 4983230072969 + 3 ^ 40 * 41791 * 2
def baseEnd_41791 : Nat := 4768637784922494715625

theorem tailTrace_41791 : CollatzResearch.WordTrace tailWord_41791 prefixEnd_41791 4768637784922494715625 := by
  unfold tailWord_41791
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524242991605819179677227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1016161994403879453118151 1524242991605819179677227)
  ·
    refine ⟨2286364487408728769515841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524242991605819179677227 2286364487408728769515841)
    ·
      refine ⟨1714773365556546577136881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2286364487408728769515841 1714773365556546577136881)
      ·
        refine ⟨1286080024167409932852661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1714773365556546577136881 1286080024167409932852661)
        ·
          refine ⟨120570002265694681204937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1286080024167409932852661 120570002265694681204937)
          ·
            refine ⟨90427501699271010903703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120570002265694681204937 90427501699271010903703)
            ·
              refine ⟨135641252548906516355555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90427501699271010903703 135641252548906516355555)
              ·
                refine ⟨203461878823359774533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135641252548906516355555 203461878823359774533333)
                ·
                  refine ⟨4768637784922494715625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 203461878823359774533333 4768637784922494715625)
                  ·
                    rfl

theorem cell22_41791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_41791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41791 prefixEnd_41791 := by exact prefixLift 41791
  have htrace : WordTrace (prefixWord ++ tailWord_41791) baseStart_41791 baseEnd_41791 := by
    simpa [prefixWord, tailWord_41791, baseEnd_41791] using wordTrace_append hprefix tailTrace_41791
  have hstable : (prefixWord ++ tailWord_41791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41791).length < 2 ^ (prefixWord ++ tailWord_41791).sum := by decide
  have hdescent : baseEnd_41791 < baseStart_41791 := by decide
  rcases family_descends (prefixWord ++ tailWord_41791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41819 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 14]
def baseStart_41819 : Nat := 118140960795 + 41819 * 2 ^ 59
def prefixEnd_41819 : Nat := 4983230072969 + 3 ^ 40 * 41819 * 2
def baseEnd_41819 : Nat := 4771832775661581482263

theorem tailTrace_41819 : CollatzResearch.WordTrace tailWord_41819 prefixEnd_41819 4771832775661581482263 := by
  unfold tailWord_41819
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525264235504379961696511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1016842823669586641131007 1525264235504379961696511)
  ·
    refine ⟨2287896353256569942544767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525264235504379961696511 2287896353256569942544767)
    ·
      refine ⟨3431844529884854913817151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287896353256569942544767 3431844529884854913817151)
      ·
        refine ⟨5147766794827282370725727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431844529884854913817151 5147766794827282370725727)
        ·
          refine ⟨7721650192240923556088591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5147766794827282370725727 7721650192240923556088591)
          ·
            refine ⟨11582475288361385334132887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7721650192240923556088591 11582475288361385334132887)
            ·
              refine ⟨17373712932542078001199331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11582475288361385334132887 17373712932542078001199331)
              ·
                refine ⟨26060569398813117001798997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17373712932542078001199331 26060569398813117001798997)
                ·
                  refine ⟨4771832775661581482263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 26060569398813117001798997 4771832775661581482263)
                  ·
                    rfl

theorem cell22_41819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_41819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41819 prefixEnd_41819 := by exact prefixLift 41819
  have htrace : WordTrace (prefixWord ++ tailWord_41819) baseStart_41819 baseEnd_41819 := by
    simpa [prefixWord, tailWord_41819, baseEnd_41819] using wordTrace_append hprefix tailTrace_41819
  have hstable : (prefixWord ++ tailWord_41819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41819).length < 2 ^ (prefixWord ++ tailWord_41819).sum := by decide
  have hdescent : baseEnd_41819 < baseStart_41819 := by decide
  rcases family_descends (prefixWord ++ tailWord_41819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41853 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 4]
def baseStart_41853 : Nat := 118140960795 + 41853 * 2 ^ 59
def prefixEnd_41853 : Nat := 4983230072969 + 3 ^ 40 * 41853 * 2
def baseEnd_41853 : Nat := 4775712407273329698895

theorem tailTrace_41853 : CollatzResearch.WordTrace tailWord_41853 prefixEnd_41853 4775712407273329698895 := by
  unfold tailWord_41853
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526504317381203768434213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1017669544920802512289475 1526504317381203768434213)
  ·
    refine ⟨286219559508975706581415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1526504317381203768434213 286219559508975706581415)
    ·
      refine ⟨429329339263463559872123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286219559508975706581415 429329339263463559872123)
      ·
        refine ⟨643994008895195339808185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429329339263463559872123 643994008895195339808185)
        ·
          refine ⟨482995506671396504856139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643994008895195339808185 482995506671396504856139)
          ·
            refine ⟨724493260007094757284209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482995506671396504856139 724493260007094757284209)
            ·
              refine ⟨543369945005321067963157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724493260007094757284209 543369945005321067963157)
              ·
                refine ⟨25470466172124425060773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 543369945005321067963157 25470466172124425060773)
                ·
                  refine ⟨4775712407273329698895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25470466172124425060773 4775712407273329698895)
                  ·
                    rfl

theorem cell22_41853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_41853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41853 prefixEnd_41853 := by exact prefixLift 41853
  have htrace : WordTrace (prefixWord ++ tailWord_41853) baseStart_41853 baseEnd_41853 := by
    simpa [prefixWord, tailWord_41853, baseEnd_41853] using wordTrace_append hprefix tailTrace_41853
  have hstable : (prefixWord ++ tailWord_41853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41853).length < 2 ^ (prefixWord ++ tailWord_41853).sum := by decide
  have hdescent : baseEnd_41853 < baseStart_41853 := by decide
  rcases family_descends (prefixWord ++ tailWord_41853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41911 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_41911 : Nat := 118140960795 + 41911 * 2 ^ 59
def prefixEnd_41911 : Nat := 4983230072969 + 3 ^ 40 * 41911 * 2
def baseEnd_41911 : Nat := 14346991807127171146507

theorem tailTrace_41911 : CollatzResearch.WordTrace tailWord_41911 prefixEnd_41911 14346991807127171146507 := by
  unfold tailWord_41911
  simp only [CollatzResearch.WordTrace]
  refine ⟨1528619751171079674045587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1019079834114053116030391 1528619751171079674045587)
  ·
    refine ⟨2292929626756619511068381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1528619751171079674045587 2292929626756619511068381)
    ·
      refine ⟨859848610033732316650643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2292929626756619511068381 859848610033732316650643)
      ·
        refine ⟨1289772915050598474975965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859848610033732316650643 1289772915050598474975965)
        ·
          refine ⟨483664843143974428115987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1289772915050598474975965 483664843143974428115987)
          ·
            refine ⟨725497264715961642173981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483664843143974428115987 725497264715961642173981)
            ·
              refine ⟨272061474268485615815243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725497264715961642173981 272061474268485615815243)
              ·
                refine ⟨408092211402728423722865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272061474268485615815243 408092211402728423722865)
                ·
                  refine ⟨306069158552046317792149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408092211402728423722865 306069158552046317792149)
                  ·
                    refine ⟨14346991807127171146507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 306069158552046317792149 14346991807127171146507)
                    ·
                      rfl

theorem cell22_41911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_41911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_41911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_41911 prefixEnd_41911 := by exact prefixLift 41911
  have htrace : WordTrace (prefixWord ++ tailWord_41911) baseStart_41911 baseEnd_41911 := by
    simpa [prefixWord, tailWord_41911, baseEnd_41911] using wordTrace_append hprefix tailTrace_41911
  have hstable : (prefixWord ++ tailWord_41911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41911).length < 2 ^ (prefixWord ++ tailWord_41911).sum := by decide
  have hdescent : baseEnd_41911 < baseStart_41911 := by decide
  rcases family_descends (prefixWord ++ tailWord_41911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42033 : List Nat := [1, 2, 2, 3, 1, 2, 4, 7]
def baseStart_42033 : Nat := 118140960795 + 42033 * 2 ^ 59
def prefixEnd_42033 : Nat := 4983230072969 + 3 ^ 40 * 42033 * 2
def baseEnd_42033 : Nat := 1598750544484391066237

theorem tailTrace_42033 : CollatzResearch.WordTrace tailWord_42033 prefixEnd_42033 1598750544484391066237 := by
  unfold tailWord_42033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533069456729094509986753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1022046304486063006657835 1533069456729094509986753)
  ·
    refine ⟨1149802092546820882490065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1533069456729094509986753 1149802092546820882490065)
    ·
      refine ⟨862351569410115661867549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149802092546820882490065 862351569410115661867549)
      ·
        refine ⟨323381838528793373200331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 862351569410115661867549 323381838528793373200331)
        ·
          refine ⟨485072757793190059800497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323381838528793373200331 485072757793190059800497)
          ·
            refine ⟨363804568344892544850373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485072757793190059800497 363804568344892544850373)
            ·
              refine ⟨68213356564667352159445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 363804568344892544850373 68213356564667352159445)
              ·
                refine ⟨1598750544484391066237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68213356564667352159445 1598750544484391066237)
                ·
                  rfl

theorem cell22_42033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 7].length) (baseStart_42033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42033 prefixEnd_42033 := by exact prefixLift 42033
  have htrace : WordTrace (prefixWord ++ tailWord_42033) baseStart_42033 baseEnd_42033 := by
    simpa [prefixWord, tailWord_42033, baseEnd_42033] using wordTrace_append hprefix tailTrace_42033
  have hstable : (prefixWord ++ tailWord_42033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42033).length < 2 ^ (prefixWord ++ tailWord_42033).sum := by decide
  have hdescent : baseEnd_42033 < baseStart_42033 := by decide
  rcases family_descends (prefixWord ++ tailWord_42033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42140 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_42140 : Nat := 118140960795 + 42140 * 2 ^ 59
def prefixEnd_42140 : Nat := 4983230072969 + 3 ^ 40 * 42140 * 2
def baseEnd_42140 : Nat := 4808461062348969056935

theorem tailTrace_42140 : CollatzResearch.WordTrace tailWord_42140 prefixEnd_42140 4808461062348969056935 := by
  unfold tailWord_42140
  simp only [CollatzResearch.WordTrace]
  refine ⟨768486033670725892065937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1024648044894301189421249 768486033670725892065937)
  ·
    refine ⟨576364525253044419049453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 768486033670725892065937 576364525253044419049453)
    ·
      refine ⟨216136696969891657143545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 576364525253044419049453 216136696969891657143545)
      ·
        refine ⟨162102522727418742857659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216136696969891657143545 162102522727418742857659)
        ·
          refine ⟨243153784091128114286489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162102522727418742857659 243153784091128114286489)
          ·
            refine ⟨182365338068346085714867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243153784091128114286489 182365338068346085714867)
            ·
              refine ⟨273548007102519128572301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182365338068346085714867 273548007102519128572301)
              ·
                refine ⟨102580502663444673214613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273548007102519128572301 102580502663444673214613)
                ·
                  refine ⟨4808461062348969056935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102580502663444673214613 4808461062348969056935)
                  ·
                    rfl

theorem cell22_42140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_42140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42140 prefixEnd_42140 := by exact prefixLift 42140
  have htrace : WordTrace (prefixWord ++ tailWord_42140) baseStart_42140 baseEnd_42140 := by
    simpa [prefixWord, tailWord_42140, baseEnd_42140] using wordTrace_append hprefix tailTrace_42140
  have hstable : (prefixWord ++ tailWord_42140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42140).length < 2 ^ (prefixWord ++ tailWord_42140).sum := by decide
  have hdescent : baseEnd_42140 < baseStart_42140 := by decide
  rcases family_descends (prefixWord ++ tailWord_42140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42170 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_42170 : Nat := 118140960795 + 42170 * 2 ^ 59
def prefixEnd_42170 : Nat := 4983230072969 + 3 ^ 40 * 42170 * 2
def baseEnd_42170 : Nat := 14435652800136828920713

theorem tailTrace_42170 : CollatzResearch.WordTrace tailWord_42170 prefixEnd_42170 14435652800136828920713 := by
  unfold tailWord_42170
  simp only [CollatzResearch.WordTrace]
  refine ⟨384516564308191726930991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1025377504821844605149309 384516564308191726930991)
  ·
    refine ⟨576774846462287590396487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384516564308191726930991 576774846462287590396487)
    ·
      refine ⟨865162269693431385594731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576774846462287590396487 865162269693431385594731)
      ·
        refine ⟨1297743404540147078392097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865162269693431385594731 1297743404540147078392097)
        ·
          refine ⟨973307553405110308794073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297743404540147078392097 973307553405110308794073)
          ·
            refine ⟨729980665053832731595555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973307553405110308794073 729980665053832731595555)
            ·
              refine ⟨1094970997580749097393333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729980665053832731595555 1094970997580749097393333)
              ·
                refine ⟨102653531023195227880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094970997580749097393333 102653531023195227880625)
                ·
                  refine ⟨76990148267396420910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102653531023195227880625 76990148267396420910469)
                  ·
                    refine ⟨14435652800136828920713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76990148267396420910469 14435652800136828920713)
                    ·
                      rfl

theorem cell22_42170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_42170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42170 prefixEnd_42170 := by exact prefixLift 42170
  have htrace : WordTrace (prefixWord ++ tailWord_42170) baseStart_42170 baseEnd_42170 := by
    simpa [prefixWord, tailWord_42170, baseEnd_42170] using wordTrace_append hprefix tailTrace_42170
  have hstable : (prefixWord ++ tailWord_42170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42170).length < 2 ^ (prefixWord ++ tailWord_42170).sum := by decide
  have hdescent : baseEnd_42170 < baseStart_42170 := by decide
  rcases family_descends (prefixWord ++ tailWord_42170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42172 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_42172 : Nat := 118140960795 + 42172 * 2 ^ 59
def prefixEnd_42172 : Nat := 4983230072969 + 3 ^ 40 * 42172 * 2
def baseEnd_42172 : Nat := 14436337441009490370707

theorem tailTrace_42172 : CollatzResearch.WordTrace tailWord_42172 prefixEnd_42172 14436337441009490370707 := by
  unfold tailWord_42172
  simp only [CollatzResearch.WordTrace]
  refine ⟨769069601612760624648385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1025426135483680832864513 769069601612760624648385)
  ·
    refine ⟨576802201209570468486289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 769069601612760624648385 576802201209570468486289)
    ·
      refine ⟨432601650907177851364717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 576802201209570468486289 432601650907177851364717)
      ·
        refine ⟨162225619090191694261769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432601650907177851364717 162225619090191694261769)
        ·
          refine ⟨121669214317643770696327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162225619090191694261769 121669214317643770696327)
          ·
            refine ⟨182503821476465656044491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121669214317643770696327 182503821476465656044491)
            ·
              refine ⟨273755732214698484066737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182503821476465656044491 273755732214698484066737)
              ·
                refine ⟨205316799161023863050053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273755732214698484066737 205316799161023863050053)
                ·
                  refine ⟨38496899842691974321885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205316799161023863050053 38496899842691974321885)
                  ·
                    refine ⟨14436337441009490370707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38496899842691974321885 14436337441009490370707)
                    ·
                      rfl

theorem cell22_42172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_42172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42172 prefixEnd_42172 := by exact prefixLift 42172
  have htrace : WordTrace (prefixWord ++ tailWord_42172) baseStart_42172 baseEnd_42172 := by
    simpa [prefixWord, tailWord_42172, baseEnd_42172] using wordTrace_append hprefix tailTrace_42172
  have hstable : (prefixWord ++ tailWord_42172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42172).length < 2 ^ (prefixWord ++ tailWord_42172).sum := by decide
  have hdescent : baseEnd_42172 < baseStart_42172 := by decide
  rcases family_descends (prefixWord ++ tailWord_42172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42174 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_42174 : Nat := 118140960795 + 42174 * 2 ^ 59
def prefixEnd_42174 : Nat := 4983230072969 + 3 ^ 40 * 42174 * 2
def baseEnd_42174 : Nat := 4812340693960717273567

theorem tailTrace_42174 : CollatzResearch.WordTrace tailWord_42174 prefixEnd_42174 4812340693960717273567 := by
  unfold tailWord_42174
  simp only [CollatzResearch.WordTrace]
  refine ⟨192276518652284448858697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1025474766145517060579717 192276518652284448858697)
  ·
    refine ⟨144207388989213336644023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192276518652284448858697 144207388989213336644023)
    ·
      refine ⟨216311083483820004966035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144207388989213336644023 216311083483820004966035)
      ·
        refine ⟨324466625225730007449053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216311083483820004966035 324466625225730007449053)
        ·
          refine ⟨121674984459648752793395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324466625225730007449053 121674984459648752793395)
          ·
            refine ⟨182512476689473129190093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121674984459648752793395 182512476689473129190093)
            ·
              refine ⟨68442178758552423446285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182512476689473129190093 68442178758552423446285)
              ·
                refine ⟨25665817034457158792357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68442178758552423446285 25665817034457158792357)
                ·
                  refine ⟨4812340693960717273567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25665817034457158792357 4812340693960717273567)
                  ·
                    rfl

theorem cell22_42174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_42174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42174 prefixEnd_42174 := by exact prefixLift 42174
  have htrace : WordTrace (prefixWord ++ tailWord_42174) baseStart_42174 baseEnd_42174 := by
    simpa [prefixWord, tailWord_42174, baseEnd_42174] using wordTrace_append hprefix tailTrace_42174
  have hstable : (prefixWord ++ tailWord_42174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42174).length < 2 ^ (prefixWord ++ tailWord_42174).sum := by decide
  have hdescent : baseEnd_42174 < baseStart_42174 := by decide
  rcases family_descends (prefixWord ++ tailWord_42174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42234 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_42234 : Nat := 118140960795 + 42234 * 2 ^ 59
def prefixEnd_42234 : Nat := 4983230072969 + 3 ^ 40 * 42234 * 2
def baseEnd_42234 : Nat := 14457561308061995320517

theorem tailTrace_42234 : CollatzResearch.WordTrace tailWord_42234 prefixEnd_42234 14457561308061995320517 := by
  unfold tailWord_42234
  simp only [CollatzResearch.WordTrace]
  refine ⟨385100132250226459513439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1026933686000603892035837 385100132250226459513439)
  ·
    refine ⟨577650198375339689270159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385100132250226459513439 577650198375339689270159)
    ·
      refine ⟨866475297563009533905239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577650198375339689270159 866475297563009533905239)
      ·
        refine ⟨1299712946344514300857859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866475297563009533905239 1299712946344514300857859)
        ·
          refine ⟨1949569419516771451286789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299712946344514300857859 1949569419516771451286789)
          ·
            refine ⟨365544266159394647116273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1949569419516771451286789 365544266159394647116273)
            ·
              refine ⟨274158199619545985337205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365544266159394647116273 274158199619545985337205)
              ·
                refine ⟨25702331214332436125363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274158199619545985337205 25702331214332436125363)
                ·
                  refine ⟨38553496821498654188045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25702331214332436125363 38553496821498654188045)
                  ·
                    refine ⟨14457561308061995320517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38553496821498654188045 14457561308061995320517)
                    ·
                      rfl

theorem cell22_42234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_42234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42234 prefixEnd_42234 := by exact prefixLift 42234
  have htrace : WordTrace (prefixWord ++ tailWord_42234) baseStart_42234 baseEnd_42234 := by
    simpa [prefixWord, tailWord_42234, baseEnd_42234] using wordTrace_append hprefix tailTrace_42234
  have hstable : (prefixWord ++ tailWord_42234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42234).length < 2 ^ (prefixWord ++ tailWord_42234).sum := by decide
  have hdescent : baseEnd_42234 < baseStart_42234 := by decide
  rcases family_descends (prefixWord ++ tailWord_42234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42245 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_42245 : Nat := 118140960795 + 42245 * 2 ^ 59
def prefixEnd_42245 : Nat := 4983230072969 + 3 ^ 40 * 42245 * 2
def baseEnd_42245 : Nat := 14461326832861633295483

theorem tailTrace_42245 : CollatzResearch.WordTrace tailWord_42245 prefixEnd_42245 14461326832861633295483 := by
  unfold tailWord_42245
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540801731961054716704189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1027201154640703144469459 1540801731961054716704189)
  ·
    refine ⟨577800649485395518764071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1540801731961054716704189 577800649485395518764071)
    ·
      refine ⟨866700974228093278146107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577800649485395518764071 866700974228093278146107)
      ·
        refine ⟨1300051461342139917219161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866700974228093278146107 1300051461342139917219161)
        ·
          refine ⟨975038596006604937914371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300051461342139917219161 975038596006604937914371)
          ·
            refine ⟨1462557894009907406871557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975038596006604937914371 1462557894009907406871557)
            ·
              refine ⟨274229605126857638788417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1462557894009907406871557 274229605126857638788417)
              ·
                refine ⟨205672203845143229091313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274229605126857638788417 205672203845143229091313)
                ·
                  refine ⟨154254152883857421818485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205672203845143229091313 154254152883857421818485)
                  ·
                    refine ⟨14461326832861633295483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154254152883857421818485 14461326832861633295483)
                    ·
                      rfl

theorem cell22_42245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_42245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42245 prefixEnd_42245 := by exact prefixLift 42245
  have htrace : WordTrace (prefixWord ++ tailWord_42245) baseStart_42245 baseEnd_42245 := by
    simpa [prefixWord, tailWord_42245, baseEnd_42245] using wordTrace_append hprefix tailTrace_42245
  have hstable : (prefixWord ++ tailWord_42245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42245).length < 2 ^ (prefixWord ++ tailWord_42245).sum := by decide
  have hdescent : baseEnd_42245 < baseStart_42245 := by decide
  rcases family_descends (prefixWord ++ tailWord_42245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42251 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 1, 3]
def baseStart_42251 : Nat := 118140960795 + 42251 * 2 ^ 59
def prefixEnd_42251 : Nat := 4983230072969 + 3 ^ 40 * 42251 * 2
def baseEnd_42251 : Nat := 14463380755479617645465

theorem tailTrace_42251 : CollatzResearch.WordTrace tailWord_42251 prefixEnd_42251 14463380755479617645465 := by
  unfold tailWord_42251
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541020569939317741422607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1027347046626211827615071 1541020569939317741422607)
  ·
    refine ⟨2311530854908976612133911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1541020569939317741422607 2311530854908976612133911)
    ·
      refine ⟨3467296282363464918200867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311530854908976612133911 3467296282363464918200867)
      ·
        refine ⟨5200944423545197377301301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467296282363464918200867 5200944423545197377301301)
        ·
          refine ⟨487588539707362254121997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5200944423545197377301301 487588539707362254121997)
          ·
            refine ⟨182845702390260845295749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487588539707362254121997 182845702390260845295749)
            ·
              refine ⟨34283569198173908492953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182845702390260845295749 34283569198173908492953)
              ·
                refine ⟨25712676898630431369715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34283569198173908492953 25712676898630431369715)
                ·
                  refine ⟨38569015347945647054573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25712676898630431369715 38569015347945647054573)
                  ·
                    refine ⟨14463380755479617645465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38569015347945647054573 14463380755479617645465)
                    ·
                      rfl

theorem cell22_42251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 3].length) (baseStart_42251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42251 prefixEnd_42251 := by exact prefixLift 42251
  have htrace : WordTrace (prefixWord ++ tailWord_42251) baseStart_42251 baseEnd_42251 := by
    simpa [prefixWord, tailWord_42251, baseEnd_42251] using wordTrace_append hprefix tailTrace_42251
  have hstable : (prefixWord ++ tailWord_42251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42251).length < 2 ^ (prefixWord ++ tailWord_42251).sum := by decide
  have hdescent : baseEnd_42251 < baseStart_42251 := by decide
  rcases family_descends (prefixWord ++ tailWord_42251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42275 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 8]
def baseStart_42275 : Nat := 118140960795 + 42275 * 2 ^ 59
def prefixEnd_42275 : Nat := 4983230072969 + 3 ^ 40 * 42275 * 2
def baseEnd_42275 : Nat := 4823865481983851681797

theorem tailTrace_42275 : CollatzResearch.WordTrace tailWord_42275 prefixEnd_42275 4823865481983851681797 := by
  unfold tailWord_42275
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541895921852369840296279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1027930614568246560197519 1541895921852369840296279)
  ·
    refine ⟨2312843882778554760444419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1541895921852369840296279 2312843882778554760444419)
    ·
      refine ⟨3469265824167832140666629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312843882778554760444419 3469265824167832140666629)
      ·
        refine ⟨650487342031468526374993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3469265824167832140666629 650487342031468526374993)
        ·
          refine ⟨487865506523601394781245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650487342031468526374993 487865506523601394781245)
          ·
            refine ⟨182949564946350523042967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487865506523601394781245 182949564946350523042967)
            ·
              refine ⟨274424347419525784564451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182949564946350523042967 274424347419525784564451)
              ·
                refine ⟨411636521129288676846677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274424347419525784564451 411636521129288676846677)
                ·
                  refine ⟨4823865481983851681797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 411636521129288676846677 4823865481983851681797)
                  ·
                    rfl

theorem cell22_42275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_42275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42275 prefixEnd_42275 := by exact prefixLift 42275
  have htrace : WordTrace (prefixWord ++ tailWord_42275) baseStart_42275 baseEnd_42275 := by
    simpa [prefixWord, tailWord_42275, baseEnd_42275] using wordTrace_append hprefix tailTrace_42275
  have hstable : (prefixWord ++ tailWord_42275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42275).length < 2 ^ (prefixWord ++ tailWord_42275).sum := by decide
  have hdescent : baseEnd_42275 < baseStart_42275 := by decide
  rcases family_descends (prefixWord ++ tailWord_42275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42277 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_42277 : Nat := 118140960795 + 42277 * 2 ^ 59
def prefixEnd_42277 : Nat := 4983230072969 + 3 ^ 40 * 42277 * 2
def baseEnd_42277 : Nat := 14472281086824216495385

theorem tailTrace_42277 : CollatzResearch.WordTrace tailWord_42277 prefixEnd_42277 14472281086824216495385 := by
  unfold tailWord_42277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541968867845124181869085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1027979245230082787912723 1541968867845124181869085)
  ·
    refine ⟨578238325441921568200907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1541968867845124181869085 578238325441921568200907)
    ·
      refine ⟨867357488162882352301361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578238325441921568200907 867357488162882352301361)
      ·
        refine ⟨650518116122161764226021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867357488162882352301361 650518116122161764226021)
        ·
          refine ⟨121972146772905330792379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 650518116122161764226021 121972146772905330792379)
          ·
            refine ⟨182958220159357996188569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121972146772905330792379 182958220159357996188569)
            ·
              refine ⟨137218665119518497141427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182958220159357996188569 137218665119518497141427)
              ·
                refine ⟨205827997679277745712141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137218665119518497141427 205827997679277745712141)
                ·
                  refine ⟨77185499129729154642053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205827997679277745712141 77185499129729154642053)
                  ·
                    refine ⟨14472281086824216495385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77185499129729154642053 14472281086824216495385)
                    ·
                      rfl

theorem cell22_42277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_42277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42277 prefixEnd_42277 := by exact prefixLift 42277
  have htrace : WordTrace (prefixWord ++ tailWord_42277) baseStart_42277 baseEnd_42277 := by
    simpa [prefixWord, tailWord_42277, baseEnd_42277] using wordTrace_append hprefix tailTrace_42277
  have hstable : (prefixWord ++ tailWord_42277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42277).length < 2 ^ (prefixWord ++ tailWord_42277).sum := by decide
  have hdescent : baseEnd_42277 < baseStart_42277 := by decide
  rcases family_descends (prefixWord ++ tailWord_42277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42292 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_42292 : Nat := 118140960795 + 42292 * 2 ^ 59
def prefixEnd_42292 : Nat := 4983230072969 + 3 ^ 40 * 42292 * 2
def baseEnd_42292 : Nat := 4825805297789725790113

theorem tailTrace_42292 : CollatzResearch.WordTrace tailWord_42292 prefixEnd_42292 4825805297789725790113 := by
  unfold tailWord_42292
  simp only [CollatzResearch.WordTrace]
  refine ⟨771257981395390871832565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1028343975193854495776753 771257981395390871832565)
  ·
    refine ⟨72305435755817894234303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 771257981395390871832565 72305435755817894234303)
    ·
      refine ⟨108458153633726841351455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72305435755817894234303 108458153633726841351455)
      ·
        refine ⟨162687230450590262027183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108458153633726841351455 162687230450590262027183)
        ·
          refine ⟨244030845675885393040775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162687230450590262027183 244030845675885393040775)
          ·
            refine ⟨366046268513828089561163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244030845675885393040775 366046268513828089561163)
            ·
              refine ⟨549069402770742134341745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366046268513828089561163 549069402770742134341745)
              ·
                refine ⟨411802052078056600756309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549069402770742134341745 411802052078056600756309)
                ·
                  refine ⟨4825805297789725790113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 411802052078056600756309 4825805297789725790113)
                  ·
                    rfl

theorem cell22_42292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_42292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42292 prefixEnd_42292 := by exact prefixLift 42292
  have htrace : WordTrace (prefixWord ++ tailWord_42292) baseStart_42292 baseEnd_42292 := by
    simpa [prefixWord, tailWord_42292, baseEnd_42292] using wordTrace_append hprefix tailTrace_42292
  have hstable : (prefixWord ++ tailWord_42292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42292).length < 2 ^ (prefixWord ++ tailWord_42292).sum := by decide
  have hdescent : baseEnd_42292 < baseStart_42292 := by decide
  rcases family_descends (prefixWord ++ tailWord_42292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42320 : List Nat := [2, 1, 1, 1, 1, 5, 2, 9]
def baseStart_42320 : Nat := 118140960795 + 42320 * 2 ^ 59
def prefixEnd_42320 : Nat := 4983230072969 + 3 ^ 40 * 42320 * 2
def baseEnd_42320 : Nat := 1609666762842937518917

theorem tailTrace_42320 : CollatzResearch.WordTrace tailWord_42320 prefixEnd_42320 1609666762842937518917 := by
  unfold tailWord_42320
  simp only [CollatzResearch.WordTrace]
  refine ⟨771768603344671262842207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1029024804459561683789609 771768603344671262842207)
  ·
    refine ⟨1157652905017006894263311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 771768603344671262842207 1157652905017006894263311)
    ·
      refine ⟨1736479357525510341394967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157652905017006894263311 1736479357525510341394967)
      ·
        refine ⟨2604719036288265512092451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736479357525510341394967 2604719036288265512092451)
        ·
          refine ⟨3907078554432398268138677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604719036288265512092451 3907078554432398268138677)
          ·
            refine ⟨366288614478037337638001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3907078554432398268138677 366288614478037337638001)
            ·
              refine ⟨274716460858528003228501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366288614478037337638001 274716460858528003228501)
              ·
                refine ⟨1609666762842937518917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 274716460858528003228501 1609666762842937518917)
                ·
                  rfl

theorem cell22_42320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_42320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42320 prefixEnd_42320 := by exact prefixLift 42320
  have htrace : WordTrace (prefixWord ++ tailWord_42320) baseStart_42320 baseEnd_42320 := by
    simpa [prefixWord, tailWord_42320, baseEnd_42320] using wordTrace_append hprefix tailTrace_42320
  have hstable : (prefixWord ++ tailWord_42320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42320).length < 2 ^ (prefixWord ++ tailWord_42320).sum := by decide
  have hdescent : baseEnd_42320 < baseStart_42320 := by decide
  rcases family_descends (prefixWord ++ tailWord_42320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42335 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_42335 : Nat := 118140960795 + 42335 * 2 ^ 59
def prefixEnd_42335 : Nat := 4983230072969 + 3 ^ 40 * 42335 * 2
def baseEnd_42335 : Nat := 14492135672131398545207

theorem tailTrace_42335 : CollatzResearch.WordTrace tailWord_42335 prefixEnd_42335 14492135672131398545207 := by
  unfold tailWord_42335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544084301635000087480459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1029389534423333391653639 1544084301635000087480459)
  ·
    refine ⟨2316126452452500131220689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544084301635000087480459 2316126452452500131220689)
    ·
      refine ⟨1737094839339375098415517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2316126452452500131220689 1737094839339375098415517)
      ·
        refine ⟨651410564752265661905819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1737094839339375098415517 651410564752265661905819)
        ·
          refine ⟨977115847128398492858729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651410564752265661905819 977115847128398492858729)
          ·
            refine ⟨732836885346298869644047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977115847128398492858729 732836885346298869644047)
            ·
              refine ⟨1099255328019448304466071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732836885346298869644047 1099255328019448304466071)
              ·
                refine ⟨1648882992029172456699107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099255328019448304466071 1648882992029172456699107)
                ·
                  refine ⟨2473324488043758685048661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648882992029172456699107 2473324488043758685048661)
                  ·
                    refine ⟨14492135672131398545207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2473324488043758685048661 14492135672131398545207)
                    ·
                      rfl

theorem cell22_42335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_42335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42335 prefixEnd_42335 := by exact prefixLift 42335
  have htrace : WordTrace (prefixWord ++ tailWord_42335) baseStart_42335 baseEnd_42335 := by
    simpa [prefixWord, tailWord_42335, baseEnd_42335] using wordTrace_append hprefix tailTrace_42335
  have hstable : (prefixWord ++ tailWord_42335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42335).length < 2 ^ (prefixWord ++ tailWord_42335).sum := by decide
  have hdescent : baseEnd_42335 < baseStart_42335 := by decide
  rcases family_descends (prefixWord ++ tailWord_42335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42343 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 4]
def baseStart_42343 : Nat := 118140960795 + 42343 * 2 ^ 59
def prefixEnd_42343 : Nat := 4983230072969 + 3 ^ 40 * 42343 * 2
def baseEnd_42343 : Nat := 4831624745207348115061

theorem tailTrace_42343 : CollatzResearch.WordTrace tailWord_42343 prefixEnd_42343 4831624745207348115061 := by
  unfold tailWord_42343
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544376085606017453771683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1029584057070678302514455 1544376085606017453771683)
  ·
    refine ⟨2316564128409026180657525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544376085606017453771683 2316564128409026180657525)
    ·
      refine ⟨217177887038346204436643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2316564128409026180657525 217177887038346204436643)
      ·
        refine ⟨325766830557519306654965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217177887038346204436643 325766830557519306654965)
        ·
          refine ⟨30540640364767434998903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 325766830557519306654965 30540640364767434998903)
          ·
            refine ⟨45810960547151152498355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30540640364767434998903 45810960547151152498355)
            ·
              refine ⟨68716440820726728747533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45810960547151152498355 68716440820726728747533)
              ·
                refine ⟨25768665307772523280325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68716440820726728747533 25768665307772523280325)
                ·
                  refine ⟨4831624745207348115061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25768665307772523280325 4831624745207348115061)
                  ·
                    rfl

theorem cell22_42343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 4].length) (baseStart_42343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42343 prefixEnd_42343 := by exact prefixLift 42343
  have htrace : WordTrace (prefixWord ++ tailWord_42343) baseStart_42343 baseEnd_42343 := by
    simpa [prefixWord, tailWord_42343, baseEnd_42343] using wordTrace_append hprefix tailTrace_42343
  have hstable : (prefixWord ++ tailWord_42343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42343).length < 2 ^ (prefixWord ++ tailWord_42343).sum := by decide
  have hdescent : baseEnd_42343 < baseStart_42343 := by decide
  rcases family_descends (prefixWord ++ tailWord_42343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42444 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_42444 : Nat := 118140960795 + 42444 * 2 ^ 59
def prefixEnd_42444 : Nat := 4983230072969 + 3 ^ 40 * 42444 * 2
def baseEnd_42444 : Nat := 4843149533230482523291

theorem tailTrace_42444 : CollatzResearch.WordTrace tailWord_42444 prefixEnd_42444 4843149533230482523291 := by
  unfold tailWord_42444
  simp only [CollatzResearch.WordTrace]
  refine ⟨774029929120055851599193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1032039905493407802132257 774029929120055851599193)
  ·
    refine ⟨580522446840041888699395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 774029929120055851599193 580522446840041888699395)
    ·
      refine ⟨870783670260062833049093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580522446840041888699395 870783670260062833049093)
      ·
        refine ⟨163271938173761781196705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 870783670260062833049093 163271938173761781196705)
        ·
          refine ⟨122453953630321335897529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163271938173761781196705 122453953630321335897529)
          ·
            refine ⟨91840465222741001923147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122453953630321335897529 91840465222741001923147)
            ·
              refine ⟨137760697834111502884721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91840465222741001923147 137760697834111502884721)
              ·
                refine ⟨103320523375583627163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137760697834111502884721 103320523375583627163541)
                ·
                  refine ⟨4843149533230482523291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103320523375583627163541 4843149533230482523291)
                  ·
                    rfl

theorem cell22_42444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_42444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42444 prefixEnd_42444 := by exact prefixLift 42444
  have htrace : WordTrace (prefixWord ++ tailWord_42444) baseStart_42444 baseEnd_42444 := by
    simpa [prefixWord, tailWord_42444, baseEnd_42444] using wordTrace_append hprefix tailTrace_42444
  have hstable : (prefixWord ++ tailWord_42444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42444).length < 2 ^ (prefixWord ++ tailWord_42444).sum := by decide
  have hdescent : baseEnd_42444 < baseStart_42444 := by decide
  rcases family_descends (prefixWord ++ tailWord_42444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42461 : List Nat := [1, 4, 3, 1, 1, 2, 1, 5, 4]
def baseStart_42461 : Nat := 118140960795 + 42461 * 2 ^ 59
def prefixEnd_42461 : Nat := 4983230072969 + 3 ^ 40 * 42461 * 2
def baseEnd_42461 : Nat := 4845089349036356631607

theorem tailTrace_42461 : CollatzResearch.WordTrace tailWord_42461 prefixEnd_42461 4845089349036356631607 := by
  unfold tailWord_42461
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548679899178523606567237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1032453266119015737711491 1548679899178523606567237)
  ·
    refine ⟨290377481095973176231357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1548679899178523606567237 290377481095973176231357)
    ·
      refine ⟨108891555410989941086759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290377481095973176231357 108891555410989941086759)
      ·
        refine ⟨163337333116484911630139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108891555410989941086759 163337333116484911630139)
        ·
          refine ⟨245005999674727367445209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163337333116484911630139 245005999674727367445209)
          ·
            refine ⟨183754499756045525583907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245005999674727367445209 183754499756045525583907)
            ·
              refine ⟨275631749634068288375861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183754499756045525583907 275631749634068288375861)
              ·
                refine ⟨25840476528193902035237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275631749634068288375861 25840476528193902035237)
                ·
                  refine ⟨4845089349036356631607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25840476528193902035237 4845089349036356631607)
                  ·
                    rfl

theorem cell22_42461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_42461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42461 prefixEnd_42461 := by exact prefixLift 42461
  have htrace : WordTrace (prefixWord ++ tailWord_42461) baseStart_42461 baseEnd_42461 := by
    simpa [prefixWord, tailWord_42461, baseEnd_42461] using wordTrace_append hprefix tailTrace_42461
  have hstable : (prefixWord ++ tailWord_42461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42461).length < 2 ^ (prefixWord ++ tailWord_42461).sum := by decide
  have hdescent : baseEnd_42461 < baseStart_42461 := by decide
  rcases family_descends (prefixWord ++ tailWord_42461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42472 : List Nat := [2, 1, 4, 1, 1, 2, 11]
def baseStart_42472 : Nat := 118140960795 + 42472 * 2 ^ 59
def prefixEnd_42472 : Nat := 4983230072969 + 3 ^ 40 * 42472 * 2
def baseEnd_42472 : Nat := 538482724885507698881

theorem tailTrace_42472 : CollatzResearch.WordTrace tailWord_42472 prefixEnd_42472 538482724885507698881 := by
  unfold tailWord_42472
  simp only [CollatzResearch.WordTrace]
  refine ⟨774540551069336242608835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1032720734759114990145113 774540551069336242608835)
  ·
    refine ⟨1161810826604004363913253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 774540551069336242608835 1161810826604004363913253)
    ·
      refine ⟨217839529988250818233735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1161810826604004363913253 217839529988250818233735)
      ·
        refine ⟨326759294982376227350603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217839529988250818233735 326759294982376227350603)
        ·
          refine ⟨490138942473564341025905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326759294982376227350603 490138942473564341025905)
          ·
            refine ⟨367604206855173255769429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490138942473564341025905 367604206855173255769429)
            ·
              refine ⟨538482724885507698881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 367604206855173255769429 538482724885507698881)
              ·
                rfl

theorem cell22_42472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 11].length) (baseStart_42472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42472 prefixEnd_42472 := by exact prefixLift 42472
  have htrace : WordTrace (prefixWord ++ tailWord_42472) baseStart_42472 baseEnd_42472 := by
    simpa [prefixWord, tailWord_42472, baseEnd_42472] using wordTrace_append hprefix tailTrace_42472
  have hstable : (prefixWord ++ tailWord_42472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42472).length < 2 ^ (prefixWord ++ tailWord_42472).sum := by decide
  have hdescent : baseEnd_42472 < baseStart_42472 := by decide
  rcases family_descends (prefixWord ++ tailWord_42472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42493 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_42493 : Nat := 118140960795 + 42493 * 2 ^ 59
def prefixEnd_42493 : Nat := 4983230072969 + 3 ^ 40 * 42493 * 2
def baseEnd_42493 : Nat := 14546222301071653094723

theorem tailTrace_42493 : CollatzResearch.WordTrace tailWord_42493 prefixEnd_42493 14546222301071653094723 := by
  unfold tailWord_42493
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549847035062593071732133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1033231356708395381154755 1549847035062593071732133)
  ·
    refine ⟨290596319074236200949775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1549847035062593071732133 290596319074236200949775)
    ·
      refine ⟨435894478611354301424663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290596319074236200949775 435894478611354301424663)
      ·
        refine ⟨653841717917031452136995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435894478611354301424663 653841717917031452136995)
        ·
          refine ⟨980762576875547178205493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653841717917031452136995 980762576875547178205493)
          ·
            refine ⟨91946491582082547956765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 980762576875547178205493 91946491582082547956765)
            ·
              refine ⟨34479934343280955483787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91946491582082547956765 34479934343280955483787)
              ·
                refine ⟨51719901514921433225681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34479934343280955483787 51719901514921433225681)
                ·
                  refine ⟨38789926136191074919261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51719901514921433225681 38789926136191074919261)
                  ·
                    refine ⟨14546222301071653094723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38789926136191074919261 14546222301071653094723)
                    ·
                      rfl

theorem cell22_42493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_42493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42493 prefixEnd_42493 := by exact prefixLift 42493
  have htrace : WordTrace (prefixWord ++ tailWord_42493) baseStart_42493 baseEnd_42493 := by
    simpa [prefixWord, tailWord_42493, baseEnd_42493] using wordTrace_append hprefix tailTrace_42493
  have hstable : (prefixWord ++ tailWord_42493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42493).length < 2 ^ (prefixWord ++ tailWord_42493).sum := by decide
  have hdescent : baseEnd_42493 < baseStart_42493 := by decide
  rcases family_descends (prefixWord ++ tailWord_42493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42506 : List Nat := [3, 1, 2, 2, 2, 4, 2, 6]
def baseStart_42506 : Nat := 118140960795 + 42506 * 2 ^ 59
def prefixEnd_42506 : Nat := 4983230072969 + 3 ^ 40 * 42506 * 2
def baseEnd_42506 : Nat := 1616741385193772502187

theorem tailTrace_42506 : CollatzResearch.WordTrace tailWord_42506 prefixEnd_42506 1616741385193772502187 := by
  unfold tailWord_42506
  simp only [CollatzResearch.WordTrace]
  refine ⟨387580296003874072988843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1033547456010330861303581 387580296003874072988843)
  ·
    refine ⟨581370444005811109483265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387580296003874072988843 581370444005811109483265)
    ·
      refine ⟨436027833004358332112449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 581370444005811109483265 436027833004358332112449)
      ·
        refine ⟨327020874753268749084337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436027833004358332112449 327020874753268749084337)
        ·
          refine ⟨245265656064951561813253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327020874753268749084337 245265656064951561813253)
          ·
            refine ⟨45987310512178417839985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245265656064951561813253 45987310512178417839985)
            ·
              refine ⟨34490482884133813379989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45987310512178417839985 34490482884133813379989)
              ·
                refine ⟨1616741385193772502187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34490482884133813379989 1616741385193772502187)
                ·
                  rfl

theorem cell22_42506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_42506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42506 prefixEnd_42506 := by exact prefixLift 42506
  have htrace : WordTrace (prefixWord ++ tailWord_42506) baseStart_42506 baseEnd_42506 := by
    simpa [prefixWord, tailWord_42506, baseEnd_42506] using wordTrace_append hprefix tailTrace_42506
  have hstable : (prefixWord ++ tailWord_42506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42506).length < 2 ^ (prefixWord ++ tailWord_42506).sum := by decide
  have hdescent : baseEnd_42506 < baseStart_42506 := by decide
  rcases family_descends (prefixWord ++ tailWord_42506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42551 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 5]
def baseStart_42551 : Nat := 118140960795 + 42551 * 2 ^ 59
def prefixEnd_42551 : Nat := 4983230072969 + 3 ^ 40 * 42551 * 2
def baseEnd_42551 : Nat := 4855358962126278381515

theorem tailTrace_42551 : CollatzResearch.WordTrace tailWord_42551 prefixEnd_42551 4855358962126278381515 := by
  unfold tailWord_42551
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551962468852468977343507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1034641645901645984895671 1551962468852468977343507)
  ·
    refine ⟨2327943703278703466015261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551962468852468977343507 2327943703278703466015261)
    ·
      refine ⟨872978888729513799755723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2327943703278703466015261 872978888729513799755723)
      ·
        refine ⟨1309468333094270699633585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872978888729513799755723 1309468333094270699633585)
        ·
          refine ⟨982101249820703024725189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309468333094270699633585 982101249820703024725189)
          ·
            refine ⟨184143984341381817135973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 982101249820703024725189 184143984341381817135973)
            ·
              refine ⟨34526997064009090712995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184143984341381817135973 34526997064009090712995)
              ·
                refine ⟨51790495596013636069493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34526997064009090712995 51790495596013636069493)
                ·
                  refine ⟨4855358962126278381515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51790495596013636069493 4855358962126278381515)
                  ·
                    rfl

theorem cell22_42551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 5].length) (baseStart_42551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42551 prefixEnd_42551 := by exact prefixLift 42551
  have htrace : WordTrace (prefixWord ++ tailWord_42551) baseStart_42551 baseEnd_42551 := by
    simpa [prefixWord, tailWord_42551, baseEnd_42551] using wordTrace_append hprefix tailTrace_42551
  have hstable : (prefixWord ++ tailWord_42551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42551).length < 2 ^ (prefixWord ++ tailWord_42551).sum := by decide
  have hdescent : baseEnd_42551 < baseStart_42551 := by decide
  rcases family_descends (prefixWord ++ tailWord_42551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42609 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_42609 : Nat := 118140960795 + 42609 * 2 ^ 59
def prefixEnd_42609 : Nat := 4983230072969 + 3 ^ 40 * 42609 * 2
def baseEnd_42609 : Nat := 14585931471686017194367

theorem tailTrace_42609 : CollatzResearch.WordTrace tailWord_42609 prefixEnd_42609 14585931471686017194367 := by
  unfold tailWord_42609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554077902642344882954881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1036051935094896588636587 1554077902642344882954881)
  ·
    refine ⟨1165558426981758662216161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1554077902642344882954881 1165558426981758662216161)
    ·
      refine ⟨874168820236318996662121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1165558426981758662216161 874168820236318996662121)
      ·
        refine ⟨655626615177239247496591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 874168820236318996662121 655626615177239247496591)
        ·
          refine ⟨983439922765858871244887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655626615177239247496591 983439922765858871244887)
          ·
            refine ⟨1475159884148788306867331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983439922765858871244887 1475159884148788306867331)
            ·
              refine ⟨2212739826223182460300997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475159884148788306867331 2212739826223182460300997)
              ·
                refine ⟨414888717416846711306437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2212739826223182460300997 414888717416846711306437)
                ·
                  refine ⟨77791634515658758369957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414888717416846711306437 77791634515658758369957)
                  ·
                    refine ⟨14585931471686017194367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77791634515658758369957 14585931471686017194367)
                    ·
                      rfl

theorem cell22_42609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_42609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42609 prefixEnd_42609 := by exact prefixLift 42609
  have htrace : WordTrace (prefixWord ++ tailWord_42609) baseStart_42609 baseEnd_42609 := by
    simpa [prefixWord, tailWord_42609, baseEnd_42609] using wordTrace_append hprefix tailTrace_42609
  have hstable : (prefixWord ++ tailWord_42609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42609).length < 2 ^ (prefixWord ++ tailWord_42609).sum := by decide
  have hdescent : baseEnd_42609 < baseStart_42609 := by decide
  rcases family_descends (prefixWord ++ tailWord_42609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42632 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_42632 : Nat := 118140960795 + 42632 * 2 ^ 59
def prefixEnd_42632 : Nat := 4983230072969 + 3 ^ 40 * 42632 * 2
def baseEnd_42632 : Nat := 14593804841721623869297

theorem tailTrace_42632 : CollatzResearch.WordTrace tailWord_42632 prefixEnd_42632 14593804841721623869297 := by
  unfold tailWord_42632
  simp only [CollatzResearch.WordTrace]
  refine ⟨777458390779509905521075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1036611187706013207361433 777458390779509905521075)
  ·
    refine ⟨1166187586169264858281613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777458390779509905521075 1166187586169264858281613)
    ·
      refine ⟨437320344813474321855605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1166187586169264858281613 437320344813474321855605)
      ·
        refine ⟨40998782326263217673963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 437320344813474321855605 40998782326263217673963)
        ·
          refine ⟨61498173489394826510945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40998782326263217673963 61498173489394826510945)
          ·
            refine ⟨46123630117046119883209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61498173489394826510945 46123630117046119883209)
            ·
              refine ⟨34592722587784589912407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46123630117046119883209 34592722587784589912407)
              ·
                refine ⟨51889083881676884868611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34592722587784589912407 51889083881676884868611)
                ·
                  refine ⟨77833625822515327302917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51889083881676884868611 77833625822515327302917)
                  ·
                    refine ⟨14593804841721623869297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77833625822515327302917 14593804841721623869297)
                    ·
                      rfl

theorem cell22_42632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_42632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42632 prefixEnd_42632 := by exact prefixLift 42632
  have htrace : WordTrace (prefixWord ++ tailWord_42632) baseStart_42632 baseEnd_42632 := by
    simpa [prefixWord, tailWord_42632, baseEnd_42632] using wordTrace_append hprefix tailTrace_42632
  have hstable : (prefixWord ++ tailWord_42632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42632).length < 2 ^ (prefixWord ++ tailWord_42632).sum := by decide
  have hdescent : baseEnd_42632 < baseStart_42632 := by decide
  rcases family_descends (prefixWord ++ tailWord_42632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42686 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_42686 : Nat := 118140960795 + 42686 * 2 ^ 59
def prefixEnd_42686 : Nat := 4983230072969 + 3 ^ 40 * 42686 * 2
def baseEnd_42686 : Nat := 4870763381761161006377

theorem tailTrace_42686 : CollatzResearch.WordTrace tailWord_42686 prefixEnd_42686 4870763381761161006377 := by
  unfold tailWord_42686
  simp only [CollatzResearch.WordTrace]
  refine ⟨194610790420423379188489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1037924215575591355671941 194610790420423379188489)
  ·
    refine ⟨145958092815317534391367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194610790420423379188489 145958092815317534391367)
    ·
      refine ⟨218937139222976301587051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145958092815317534391367 218937139222976301587051)
      ·
        refine ⟨328405708834464452380577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218937139222976301587051 328405708834464452380577)
        ·
          refine ⟨246304281625848339285433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328405708834464452380577 246304281625848339285433)
          ·
            refine ⟨184728211219386254464075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246304281625848339285433 184728211219386254464075)
            ·
              refine ⟨277092316829079381696113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184728211219386254464075 277092316829079381696113)
              ·
                refine ⟨207819237621809536272085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277092316829079381696113 207819237621809536272085)
                ·
                  refine ⟨4870763381761161006377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 207819237621809536272085 4870763381761161006377)
                  ·
                    rfl

theorem cell22_42686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_42686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42686 prefixEnd_42686 := by exact prefixLift 42686
  have htrace : WordTrace (prefixWord ++ tailWord_42686) baseStart_42686 baseEnd_42686 := by
    simpa [prefixWord, tailWord_42686, baseEnd_42686] using wordTrace_append hprefix tailTrace_42686
  have hstable : (prefixWord ++ tailWord_42686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42686).length < 2 ^ (prefixWord ++ tailWord_42686).sum := by decide
  have hdescent : baseEnd_42686 < baseStart_42686 := by decide
  rcases family_descends (prefixWord ++ tailWord_42686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42733 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_42733 : Nat := 118140960795 + 42733 * 2 ^ 59
def prefixEnd_42733 : Nat := 4983230072969 + 3 ^ 40 * 42733 * 2
def baseEnd_42733 : Nat := 14628379205791027093987

theorem tailTrace_42733 : CollatzResearch.WordTrace tailWord_42733 prefixEnd_42733 14628379205791027093987 := by
  unfold tailWord_42733
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558600554193114060468853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1039067036128742706979235 1558600554193114060468853)
  ·
    refine ⟨146118801955604443168955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1558600554193114060468853 146118801955604443168955)
    ·
      refine ⟨219178202933406664753433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146118801955604443168955 219178202933406664753433)
      ·
        refine ⟨164383652200054998565075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219178202933406664753433 164383652200054998565075)
        ·
          refine ⟨246575478300082497847613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164383652200054998565075 246575478300082497847613)
          ·
            refine ⟨92465804362530936692855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246575478300082497847613 92465804362530936692855)
            ·
              refine ⟨138698706543796405039283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92465804362530936692855 138698706543796405039283)
              ·
                refine ⟨208048059815694607558925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138698706543796405039283 208048059815694607558925)
                ·
                  refine ⟨78018022430885477834597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208048059815694607558925 78018022430885477834597)
                  ·
                    refine ⟨14628379205791027093987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78018022430885477834597 14628379205791027093987)
                    ·
                      rfl

theorem cell22_42733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_42733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42733 prefixEnd_42733 := by exact prefixLift 42733
  have htrace : WordTrace (prefixWord ++ tailWord_42733) baseStart_42733 baseEnd_42733 := by
    simpa [prefixWord, tailWord_42733, baseEnd_42733] using wordTrace_append hprefix tailTrace_42733
  have hstable : (prefixWord ++ tailWord_42733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42733).length < 2 ^ (prefixWord ++ tailWord_42733).sum := by decide
  have hdescent : baseEnd_42733 < baseStart_42733 := by decide
  rcases family_descends (prefixWord ++ tailWord_42733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42748 : List Nat := [2, 2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_42748 : Nat := 118140960795 + 42748 * 2 ^ 59
def prefixEnd_42748 : Nat := 4983230072969 + 3 ^ 40 * 42748 * 2
def baseEnd_42748 : Nat := 4877838004111995989647

theorem tailTrace_42748 : CollatzResearch.WordTrace tailWord_42748 prefixEnd_42748 4877838004111995989647 := by
  unfold tailWord_42748
  simp only [CollatzResearch.WordTrace]
  refine ⟨779573824569385811132449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1039431766092514414843265 779573824569385811132449)
  ·
    refine ⟨584680368427039358349337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 779573824569385811132449 584680368427039358349337)
    ·
      refine ⟨438510276320279518762003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584680368427039358349337 438510276320279518762003)
      ·
        refine ⟨657765414480419278143005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438510276320279518762003 657765414480419278143005)
        ·
          refine ⟨246662030430157229303627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 657765414480419278143005 246662030430157229303627)
          ·
            refine ⟨369993045645235843955441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246662030430157229303627 369993045645235843955441)
            ·
              refine ⟨277494784233926882966581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369993045645235843955441 277494784233926882966581)
              ·
                refine ⟨26015136021930645278117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 277494784233926882966581 26015136021930645278117)
                ·
                  refine ⟨4877838004111995989647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26015136021930645278117 4877838004111995989647)
                  ·
                    rfl

theorem cell22_42748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_42748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42748 prefixEnd_42748 := by exact prefixLift 42748
  have htrace : WordTrace (prefixWord ++ tailWord_42748) baseStart_42748 baseEnd_42748 := by
    simpa [prefixWord, tailWord_42748, baseEnd_42748] using wordTrace_append hprefix tailTrace_42748
  have hstable : (prefixWord ++ tailWord_42748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42748).length < 2 ^ (prefixWord ++ tailWord_42748).sum := by decide
  have hdescent : baseEnd_42748 < baseStart_42748 := by decide
  rcases family_descends (prefixWord ++ tailWord_42748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42763 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 2, 3]
def baseStart_42763 : Nat := 118140960795 + 42763 * 2 ^ 59
def prefixEnd_42763 : Nat := 4983230072969 + 3 ^ 40 * 42763 * 2
def baseEnd_42763 : Nat := 14638648818880948843895

theorem tailTrace_42763 : CollatzResearch.WordTrace tailWord_42763 prefixEnd_42763 14638648818880948843895 := by
  unfold tailWord_42763
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559694744084429184060943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1039796496056286122707295 1559694744084429184060943)
  ·
    refine ⟨2339542116126643776091415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1559694744084429184060943 2339542116126643776091415)
    ·
      refine ⟨3509313174189965664137123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339542116126643776091415 3509313174189965664137123)
      ·
        refine ⟨5263969761284948496205685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509313174189965664137123 5263969761284948496205685)
        ·
          refine ⟨493497165120463921519283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5263969761284948496205685 493497165120463921519283)
          ·
            refine ⟨740245747680695882278925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493497165120463921519283 740245747680695882278925)
            ·
              refine ⟨277592155380260955854597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 740245747680695882278925 277592155380260955854597)
              ·
                refine ⟨52048529133798929222737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277592155380260955854597 52048529133798929222737)
                ·
                  refine ⟨39036396850349196917053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52048529133798929222737 39036396850349196917053)
                  ·
                    refine ⟨14638648818880948843895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39036396850349196917053 14638648818880948843895)
                    ·
                      rfl

theorem cell22_42763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3].length) (baseStart_42763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42763 prefixEnd_42763 := by exact prefixLift 42763
  have htrace : WordTrace (prefixWord ++ tailWord_42763) baseStart_42763 baseEnd_42763 := by
    simpa [prefixWord, tailWord_42763, baseEnd_42763] using wordTrace_append hprefix tailTrace_42763
  have hstable : (prefixWord ++ tailWord_42763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42763).length < 2 ^ (prefixWord ++ tailWord_42763).sum := by decide
  have hdescent : baseEnd_42763 < baseStart_42763 := by decide
  rcases family_descends (prefixWord ++ tailWord_42763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42776 : List Nat := [2, 1, 2, 3, 1, 1, 5, 7]
def baseStart_42776 : Nat := 118140960795 + 42776 * 2 ^ 59
def prefixEnd_42776 : Nat := 4983230072969 + 3 ^ 40 * 42776 * 2
def baseEnd_42776 : Nat := 1627010998283694252095

theorem tailTrace_42776 : CollatzResearch.WordTrace tailWord_42776 prefixEnd_42776 1627010998283694252095 := by
  unfold tailWord_42776
  simp only [CollatzResearch.WordTrace]
  refine ⟨780084446518666202142091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1040112595358221602856121 780084446518666202142091)
  ·
    refine ⟨1170126669777999303213137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 780084446518666202142091 1170126669777999303213137)
    ·
      refine ⟨877595002333499477409853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1170126669777999303213137 877595002333499477409853)
      ·
        refine ⟨329098125875062304028695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 877595002333499477409853 329098125875062304028695)
        ·
          refine ⟨493647188812593456043043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329098125875062304028695 493647188812593456043043)
          ·
            refine ⟨740470783218890184064565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493647188812593456043043 740470783218890184064565)
            ·
              refine ⟨69419135926770954756053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 740470783218890184064565 69419135926770954756053)
              ·
                refine ⟨1627010998283694252095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69419135926770954756053 1627010998283694252095)
                ·
                  rfl

theorem cell22_42776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_42776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42776 prefixEnd_42776 := by exact prefixLift 42776
  have htrace : WordTrace (prefixWord ++ tailWord_42776) baseStart_42776 baseEnd_42776 := by
    simpa [prefixWord, tailWord_42776, baseEnd_42776] using wordTrace_append hprefix tailTrace_42776
  have hstable : (prefixWord ++ tailWord_42776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42776).length < 2 ^ (prefixWord ++ tailWord_42776).sum := by decide
  have hdescent : baseEnd_42776 < baseStart_42776 := by decide
  rcases family_descends (prefixWord ++ tailWord_42776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42782 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_42782 : Nat := 118140960795 + 42782 * 2 ^ 59
def prefixEnd_42782 : Nat := 4983230072969 + 3 ^ 40 * 42782 * 2
def baseEnd_42782 : Nat := 4881717635723744206279

theorem tailTrace_42782 : CollatzResearch.WordTrace tailWord_42782 prefixEnd_42782 4881717635723744206279 := by
  unfold tailWord_42782
  simp only [CollatzResearch.WordTrace]
  refine ⟨195048466376949428625325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1040258487343730286001733 195048466376949428625325)
  ·
    refine ⟨73143174891356035734497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195048466376949428625325 73143174891356035734497)
    ·
      refine ⟨54857381168517026800873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73143174891356035734497 54857381168517026800873)
      ·
        refine ⟨41143035876387770100655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54857381168517026800873 41143035876387770100655)
        ·
          refine ⟨61714553814581655150983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41143035876387770100655 61714553814581655150983)
          ·
            refine ⟨92571830721872482726475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61714553814581655150983 92571830721872482726475)
            ·
              refine ⟨138857746082808724089713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92571830721872482726475 138857746082808724089713)
              ·
                refine ⟨104143309562106543067285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138857746082808724089713 104143309562106543067285)
                ·
                  refine ⟨4881717635723744206279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104143309562106543067285 4881717635723744206279)
                  ·
                    rfl

theorem cell22_42782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_42782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42782 prefixEnd_42782 := by exact prefixLift 42782
  have htrace : WordTrace (prefixWord ++ tailWord_42782) baseStart_42782 baseEnd_42782 := by
    simpa [prefixWord, tailWord_42782, baseEnd_42782] using wordTrace_append hprefix tailTrace_42782
  have hstable : (prefixWord ++ tailWord_42782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42782).length < 2 ^ (prefixWord ++ tailWord_42782).sum := by decide
  have hdescent : baseEnd_42782 < baseStart_42782 := by decide
  rcases family_descends (prefixWord ++ tailWord_42782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42821 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 7]
def baseStart_42821 : Nat := 118140960795 + 42821 * 2 ^ 59
def prefixEnd_42821 : Nat := 4983230072969 + 3 ^ 40 * 42821 * 2
def baseEnd_42821 : Nat := 4886167801396043631239

theorem tailTrace_42821 : CollatzResearch.WordTrace tailWord_42821 prefixEnd_42821 4886167801396043631239 := by
  unfold tailWord_42821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561810177874305089672317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1041206785249536726448211 1561810177874305089672317)
  ·
    refine ⟨585678816702864408627119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1561810177874305089672317 585678816702864408627119)
    ·
      refine ⟨878518225054296612940679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585678816702864408627119 878518225054296612940679)
      ·
        refine ⟨1317777337581444919411019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878518225054296612940679 1317777337581444919411019)
        ·
          refine ⟨1976666006372167379116529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317777337581444919411019 1976666006372167379116529)
          ·
            refine ⟨1482499504779125534337397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976666006372167379116529 1482499504779125534337397)
            ·
              refine ⟨138984328573043018844131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1482499504779125534337397 138984328573043018844131)
              ·
                refine ⟨208476492859564528266197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138984328573043018844131 208476492859564528266197)
                ·
                  refine ⟨4886167801396043631239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 208476492859564528266197 4886167801396043631239)
                  ·
                    rfl

theorem cell22_42821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_42821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42821 prefixEnd_42821 := by exact prefixLift 42821
  have htrace : WordTrace (prefixWord ++ tailWord_42821) baseStart_42821 baseEnd_42821 := by
    simpa [prefixWord, tailWord_42821, baseEnd_42821] using wordTrace_append hprefix tailTrace_42821
  have hstable : (prefixWord ++ tailWord_42821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42821).length < 2 ^ (prefixWord ++ tailWord_42821).sum := by decide
  have hdescent : baseEnd_42821 < baseStart_42821 := by decide
  rcases family_descends (prefixWord ++ tailWord_42821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42825 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 1, 3]
def baseStart_42825 : Nat := 118140960795 + 42825 * 2 ^ 59
def prefixEnd_42825 : Nat := 4983230072969 + 3 ^ 40 * 42825 * 2
def baseEnd_42825 : Nat := 14659872685933453793705

theorem tailTrace_42825 : CollatzResearch.WordTrace tailWord_42825 prefixEnd_42825 14659872685933453793705 := by
  unfold tailWord_42825
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561956069859813772817929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1041304046573209181878619 1561956069859813772817929)
  ·
    refine ⟨1171467052394860329613447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1561956069859813772817929 1171467052394860329613447)
    ·
      refine ⟨1757200578592290494420171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1171467052394860329613447 1757200578592290494420171)
      ·
        refine ⟨2635800867888435741630257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757200578592290494420171 2635800867888435741630257)
        ·
          refine ⟨1976850650916326806222693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2635800867888435741630257 1976850650916326806222693)
          ·
            refine ⟨370659497046811276166755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1976850650916326806222693 370659497046811276166755)
            ·
              refine ⟨555989245570216914250133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370659497046811276166755 555989245570216914250133)
              ·
                refine ⟨26061995886103917855475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 555989245570216914250133 26061995886103917855475)
                ·
                  refine ⟨39092993829155876783213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26061995886103917855475 39092993829155876783213)
                  ·
                    refine ⟨14659872685933453793705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39092993829155876783213 14659872685933453793705)
                    ·
                      rfl

theorem cell22_42825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_42825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42825 prefixEnd_42825 := by exact prefixLift 42825
  have htrace : WordTrace (prefixWord ++ tailWord_42825) baseStart_42825 baseEnd_42825 := by
    simpa [prefixWord, tailWord_42825, baseEnd_42825] using wordTrace_append hprefix tailTrace_42825
  have hstable : (prefixWord ++ tailWord_42825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42825).length < 2 ^ (prefixWord ++ tailWord_42825).sum := by decide
  have hdescent : baseEnd_42825 < baseStart_42825 := by decide
  rcases family_descends (prefixWord ++ tailWord_42825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42883 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 6]
def baseStart_42883 : Nat := 118140960795 + 42883 * 2 ^ 59
def prefixEnd_42883 : Nat := 4983230072969 + 3 ^ 40 * 42883 * 2
def baseEnd_42883 : Nat := 4893242423746878614509

theorem tailTrace_42883 : CollatzResearch.WordTrace tailWord_42883 prefixEnd_42883 4893242423746878614509 := by
  unfold tailWord_42883
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564071503649689678429303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1042714335766459785619535 1564071503649689678429303)
  ·
    refine ⟨2346107255474534517643955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564071503649689678429303 2346107255474534517643955)
    ·
      refine ⟨3519160883211801776465933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346107255474534517643955 3519160883211801776465933)
      ·
        refine ⟨1319685331204425666174725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3519160883211801776465933 1319685331204425666174725)
        ·
          refine ⟨247440999600829812407761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1319685331204425666174725 247440999600829812407761)
          ·
            refine ⟨185580749700622359305821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247440999600829812407761 185580749700622359305821)
            ·
              refine ⟨69592781137733384739683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185580749700622359305821 69592781137733384739683)
              ·
                refine ⟨104389171706600077109525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69592781137733384739683 104389171706600077109525)
                ·
                  refine ⟨4893242423746878614509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104389171706600077109525 4893242423746878614509)
                  ·
                    rfl

theorem cell22_42883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 6].length) (baseStart_42883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42883 prefixEnd_42883 := by exact prefixLift 42883
  have htrace : WordTrace (prefixWord ++ tailWord_42883) baseStart_42883 baseEnd_42883 := by
    simpa [prefixWord, tailWord_42883, baseEnd_42883] using wordTrace_append hprefix tailTrace_42883
  have hstable : (prefixWord ++ tailWord_42883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42883).length < 2 ^ (prefixWord ++ tailWord_42883).sum := by decide
  have hdescent : baseEnd_42883 < baseStart_42883 := by decide
  rcases family_descends (prefixWord ++ tailWord_42883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42958 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_42958 : Nat := 118140960795 + 42958 * 2 ^ 59
def prefixEnd_42958 : Nat := 4983230072969 + 3 ^ 40 * 42958 * 2
def baseEnd_42958 : Nat := 14705401303965440218297

theorem tailTrace_42958 : CollatzResearch.WordTrace tailWord_42958 prefixEnd_42958 14705401303965440218297 := by
  unfold tailWord_42958
  simp only [CollatzResearch.WordTrace]
  refine ⟨195850872297247185926191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1044537985585318324939685 195850872297247185926191)
  ·
    refine ⟨293776308445870778889287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195850872297247185926191 293776308445870778889287)
    ·
      refine ⟨440664462668806168333931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293776308445870778889287 440664462668806168333931)
      ·
        refine ⟨660996694003209252500897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440664462668806168333931 660996694003209252500897)
        ·
          refine ⟨495747520502406939375673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660996694003209252500897 495747520502406939375673)
          ·
            refine ⟨371810640376805204531755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495747520502406939375673 371810640376805204531755)
            ·
              refine ⟨557715960565207806797633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371810640376805204531755 557715960565207806797633)
              ·
                refine ⟨418286970423905855098225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557715960565207806797633 418286970423905855098225)
                ·
                  refine ⟨313715227817929391323669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418286970423905855098225 313715227817929391323669)
                  ·
                    refine ⟨14705401303965440218297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 313715227817929391323669 14705401303965440218297)
                    ·
                      rfl

theorem cell22_42958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_42958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42958 prefixEnd_42958 := by exact prefixLift 42958
  have htrace : WordTrace (prefixWord ++ tailWord_42958) baseStart_42958 baseEnd_42958 := by
    simpa [prefixWord, tailWord_42958, baseEnd_42958] using wordTrace_append hprefix tailTrace_42958
  have hstable : (prefixWord ++ tailWord_42958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42958).length < 2 ^ (prefixWord ++ tailWord_42958).sum := by decide
  have hdescent : baseEnd_42958 < baseStart_42958 := by decide
  rcases family_descends (prefixWord ++ tailWord_42958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42962 : List Nat := [3, 2, 2, 3, 2, 1, 3, 6]
def baseStart_42962 : Nat := 118140960795 + 42962 * 2 ^ 59
def prefixEnd_42962 : Nat := 4983230072969 + 3 ^ 40 * 42962 * 2
def baseEnd_42962 : Nat := 1634085620634529235365

theorem tailTrace_42962 : CollatzResearch.WordTrace tailWord_42962 prefixEnd_42962 1634085620634529235365 := by
  unfold tailWord_42962
  simp only [CollatzResearch.WordTrace]
  refine ⟨391738217590871542638785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1044635246908990780370093 391738217590871542638785)
  ·
    refine ⟨293803663193153656979089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 391738217590871542638785 293803663193153656979089)
    ·
      refine ⟨220352747394865242734317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293803663193153656979089 220352747394865242734317)
      ·
        refine ⟨82632280273074466025369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220352747394865242734317 82632280273074466025369)
        ·
          refine ⟨61974210204805849519027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82632280273074466025369 61974210204805849519027)
          ·
            refine ⟨92961315307208774278541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61974210204805849519027 92961315307208774278541)
            ·
              refine ⟨34860493240203290354453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92961315307208774278541 34860493240203290354453)
              ·
                refine ⟨1634085620634529235365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34860493240203290354453 1634085620634529235365)
                ·
                  rfl

theorem cell22_42962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_42962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42962 prefixEnd_42962 := by exact prefixLift 42962
  have htrace : WordTrace (prefixWord ++ tailWord_42962) baseStart_42962 baseEnd_42962 := by
    simpa [prefixWord, tailWord_42962, baseEnd_42962] using wordTrace_append hprefix tailTrace_42962
  have hstable : (prefixWord ++ tailWord_42962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42962).length < 2 ^ (prefixWord ++ tailWord_42962).sum := by decide
  have hdescent : baseEnd_42962 < baseStart_42962 := by decide
  rcases family_descends (prefixWord ++ tailWord_42962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42977 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 1, 3]
def baseStart_42977 : Nat := 118140960795 + 42977 * 2 ^ 59
def prefixEnd_42977 : Nat := 4983230072969 + 3 ^ 40 * 42977 * 2
def baseEnd_42977 : Nat := 14711905392255723993239

theorem tailTrace_42977 : CollatzResearch.WordTrace tailWord_42977 prefixEnd_42977 14711905392255723993239 := by
  unfold tailWord_42977
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567499965309143732351185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1044999976872762488234123 1567499965309143732351185)
  ·
    refine ⟨1175624973981857799263389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1567499965309143732351185 1175624973981857799263389)
    ·
      refine ⟨440859365243196674723771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1175624973981857799263389 440859365243196674723771)
      ·
        refine ⟨661289047864795012085657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440859365243196674723771 661289047864795012085657)
        ·
          refine ⟨495966785898596259064243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661289047864795012085657 495966785898596259064243)
          ·
            refine ⟨743950178847894388596365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495966785898596259064243 743950178847894388596365)
            ·
              refine ⟨278981317067960395723637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743950178847894388596365 278981317067960395723637)
              ·
                refine ⟨26154498475121287099091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278981317067960395723637 26154498475121287099091)
                ·
                  refine ⟨39231747712681930648637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26154498475121287099091 39231747712681930648637)
                  ·
                    refine ⟨14711905392255723993239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39231747712681930648637 14711905392255723993239)
                    ·
                      rfl

theorem cell22_42977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_42977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42977 prefixEnd_42977 := by exact prefixLift 42977
  have htrace : WordTrace (prefixWord ++ tailWord_42977) baseStart_42977 baseEnd_42977 := by
    simpa [prefixWord, tailWord_42977, baseEnd_42977] using wordTrace_append hprefix tailTrace_42977
  have hstable : (prefixWord ++ tailWord_42977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42977).length < 2 ^ (prefixWord ++ tailWord_42977).sum := by decide
  have hdescent : baseEnd_42977 < baseStart_42977 := by decide
  rcases family_descends (prefixWord ++ tailWord_42977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42990 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_42990 : Nat := 118140960795 + 42990 * 2 ^ 59
def prefixEnd_42990 : Nat := 4983230072969 + 3 ^ 40 * 42990 * 2
def baseEnd_42990 : Nat := 4905451852642674472733

theorem tailTrace_42990 : CollatzResearch.WordTrace tailWord_42990 prefixEnd_42990 4905451852642674472733 := by
  unfold tailWord_42990
  simp only [CollatzResearch.WordTrace]
  refine ⟨195996764282755869071803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1045316076174697968382949 195996764282755869071803)
  ·
    refine ⟨293995146424133803607705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195996764282755869071803 293995146424133803607705)
    ·
      refine ⟨220496359818100352705779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293995146424133803607705 220496359818100352705779)
      ·
        refine ⟨330744539727150529058669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220496359818100352705779 330744539727150529058669)
        ·
          refine ⟨124029202397681448397001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330744539727150529058669 124029202397681448397001)
          ·
            refine ⟨93021901798261086297751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124029202397681448397001 93021901798261086297751)
            ·
              refine ⟨139532852697391629446627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93021901798261086297751 139532852697391629446627)
              ·
                refine ⟨209299279046087444169941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139532852697391629446627 209299279046087444169941)
                ·
                  refine ⟨4905451852642674472733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 209299279046087444169941 4905451852642674472733)
                  ·
                    rfl

theorem cell22_42990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_42990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_42990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_42990 prefixEnd_42990 := by exact prefixLift 42990
  have htrace : WordTrace (prefixWord ++ tailWord_42990) baseStart_42990 baseEnd_42990 := by
    simpa [prefixWord, tailWord_42990, baseEnd_42990] using wordTrace_append hprefix tailTrace_42990
  have hstable : (prefixWord ++ tailWord_42990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42990).length < 2 ^ (prefixWord ++ tailWord_42990).sum := by decide
  have hdescent : baseEnd_42990 < baseStart_42990 := by decide
  rcases family_descends (prefixWord ++ tailWord_42990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43003 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_43003 : Nat := 118140960795 + 43003 * 2 ^ 59
def prefixEnd_43003 : Nat := 4983230072969 + 3 ^ 40 * 43003 * 2
def baseEnd_43003 : Nat := 14720805723600322843159

theorem tailTrace_43003 : CollatzResearch.WordTrace tailWord_43003 prefixEnd_43003 14720805723600322843159 := by
  unfold tailWord_43003
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568448263214950172797663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1045632175476633448531775 1568448263214950172797663)
  ·
    refine ⟨2352672394822425259196495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1568448263214950172797663 2352672394822425259196495)
    ·
      refine ⟨3529008592233637888794743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2352672394822425259196495 3529008592233637888794743)
      ·
        refine ⟨5293512888350456833192115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529008592233637888794743 5293512888350456833192115)
        ·
          refine ⟨7940269332525685249788173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293512888350456833192115 7940269332525685249788173)
          ·
            refine ⟨2977600999697131968670565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7940269332525685249788173 2977600999697131968670565)
            ·
              refine ⟨558300187443212244125731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2977600999697131968670565 558300187443212244125731)
              ·
                refine ⟨837450281164818366188597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558300187443212244125731 837450281164818366188597)
                ·
                  refine ⟨78510963859201721830181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 837450281164818366188597 78510963859201721830181)
                  ·
                    refine ⟨14720805723600322843159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78510963859201721830181 14720805723600322843159)
                    ·
                      rfl

theorem cell22_43003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_43003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43003 prefixEnd_43003 := by exact prefixLift 43003
  have htrace : WordTrace (prefixWord ++ tailWord_43003) baseStart_43003 baseEnd_43003 := by
    simpa [prefixWord, tailWord_43003, baseEnd_43003] using wordTrace_append hprefix tailTrace_43003
  have hstable : (prefixWord ++ tailWord_43003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43003).length < 2 ^ (prefixWord ++ tailWord_43003).sum := by decide
  have hdescent : baseEnd_43003 < baseStart_43003 := by decide
  rcases family_descends (prefixWord ++ tailWord_43003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43033 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_43033 : Nat := 118140960795 + 43033 * 2 ^ 59
def prefixEnd_43033 : Nat := 4983230072969 + 3 ^ 40 * 43033 * 2
def baseEnd_43033 : Nat := 14731075336690244593067

theorem tailTrace_43033 : CollatzResearch.WordTrace tailWord_43033 prefixEnd_43033 14731075336690244593067 := by
  unfold tailWord_43033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569542453106265296389753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1046361635404176864259835 1569542453106265296389753)
  ·
    refine ⟨1177156839829698972292315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1569542453106265296389753 1177156839829698972292315)
    ·
      refine ⟨1765735259744548458438473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177156839829698972292315 1765735259744548458438473)
      ·
        refine ⟨1324301444808411343828855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1765735259744548458438473 1324301444808411343828855)
        ·
          refine ⟨1986452167212617015743283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324301444808411343828855 1986452167212617015743283)
          ·
            refine ⟨2979678250818925523614925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986452167212617015743283 2979678250818925523614925)
            ·
              refine ⟨1117379344057097071355597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2979678250818925523614925 1117379344057097071355597)
              ·
                refine ⟨419017254021411401758349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1117379344057097071355597 419017254021411401758349)
                ·
                  refine ⟨157131470258029275659381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419017254021411401758349 157131470258029275659381)
                  ·
                    refine ⟨14731075336690244593067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157131470258029275659381 14731075336690244593067)
                    ·
                      rfl

theorem cell22_43033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_43033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43033 prefixEnd_43033 := by exact prefixLift 43033
  have htrace : WordTrace (prefixWord ++ tailWord_43033) baseStart_43033 baseEnd_43033 := by
    simpa [prefixWord, tailWord_43033, baseEnd_43033] using wordTrace_append hprefix tailTrace_43033
  have hstable : (prefixWord ++ tailWord_43033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43033).length < 2 ^ (prefixWord ++ tailWord_43033).sum := by decide
  have hdescent : baseEnd_43033 < baseStart_43033 := by decide
  rcases family_descends (prefixWord ++ tailWord_43033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43035 : List Nat := [1, 1, 1, 1, 1, 1, 3, 9, 4]
def baseStart_43035 : Nat := 118140960795 + 43035 * 2 ^ 59
def prefixEnd_43035 : Nat := 4983230072969 + 3 ^ 40 * 43035 * 2
def baseEnd_43035 : Nat := 4910586659187635347687

theorem tailTrace_43035 : CollatzResearch.WordTrace tailWord_43035 prefixEnd_43035 4910586659187635347687 := by
  unfold tailWord_43035
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569615399099019637962559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1046410266066013091975039 1569615399099019637962559)
  ·
    refine ⟨2354423098648529456943839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1569615399099019637962559 2354423098648529456943839)
    ·
      refine ⟨3531634647972794185415759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354423098648529456943839 3531634647972794185415759)
      ·
        refine ⟨5297451971959191278123639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531634647972794185415759 5297451971959191278123639)
        ·
          refine ⟨7946177957938786917185459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297451971959191278123639 7946177957938786917185459)
          ·
            refine ⟨11919266936908180375778189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946177957938786917185459 11919266936908180375778189)
            ·
              refine ⟨4469725101340567640916821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11919266936908180375778189 4469725101340567640916821)
              ·
                refine ⟨26189795515667388520997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4469725101340567640916821 26189795515667388520997)
                ·
                  refine ⟨4910586659187635347687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26189795515667388520997 4910586659187635347687)
                  ·
                    rfl

theorem cell22_43035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 4].length) (baseStart_43035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43035 prefixEnd_43035 := by exact prefixLift 43035
  have htrace : WordTrace (prefixWord ++ tailWord_43035) baseStart_43035 baseEnd_43035 := by
    simpa [prefixWord, tailWord_43035, baseEnd_43035] using wordTrace_append hprefix tailTrace_43035
  have hstable : (prefixWord ++ tailWord_43035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43035).length < 2 ^ (prefixWord ++ tailWord_43035).sum := by decide
  have hdescent : baseEnd_43035 < baseStart_43035 := by decide
  rcases family_descends (prefixWord ++ tailWord_43035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43037 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_43037 : Nat := 118140960795 + 43037 * 2 ^ 59
def prefixEnd_43037 : Nat := 4983230072969 + 3 ^ 40 * 43037 * 2
def baseEnd_43037 : Nat := 14732444618435567493055

theorem tailTrace_43037 : CollatzResearch.WordTrace tailWord_43037 prefixEnd_43037 14732444618435567493055 := by
  unfold tailWord_43037
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569688345091773979535365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1046458896727849319690243 1569688345091773979535365)
  ·
    refine ⟨294316564704707621162881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1569688345091773979535365 294316564704707621162881)
    ·
      refine ⟨220737423528530715872161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294316564704707621162881 220737423528530715872161)
      ·
        refine ⟨165553067646398036904121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220737423528530715872161 165553067646398036904121)
        ·
          refine ⟨124164800734798527678091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165553067646398036904121 124164800734798527678091)
          ·
            refine ⟨186247201102197791517137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124164800734798527678091 186247201102197791517137)
            ·
              refine ⟨139685400826648343637853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186247201102197791517137 139685400826648343637853)
              ·
                refine ⟨52382025309993128864195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139685400826648343637853 52382025309993128864195)
                ·
                  refine ⟨78573037964989693296293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52382025309993128864195 78573037964989693296293)
                  ·
                    refine ⟨14732444618435567493055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78573037964989693296293 14732444618435567493055)
                    ·
                      rfl

theorem cell22_43037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_43037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43037 prefixEnd_43037 := by exact prefixLift 43037
  have htrace : WordTrace (prefixWord ++ tailWord_43037) baseStart_43037 baseEnd_43037 := by
    simpa [prefixWord, tailWord_43037, baseEnd_43037] using wordTrace_append hprefix tailTrace_43037
  have hstable : (prefixWord ++ tailWord_43037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43037).length < 2 ^ (prefixWord ++ tailWord_43037).sum := by decide
  have hdescent : baseEnd_43037 < baseStart_43037 := by decide
  rcases family_descends (prefixWord ++ tailWord_43037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43063 : List Nat := [1, 1, 3, 1, 2, 2, 3, 9]
def baseStart_43063 : Nat := 118140960795 + 43063 * 2 ^ 59
def prefixEnd_43063 : Nat := 4983230072969 + 3 ^ 40 * 43063 * 2
def baseEnd_43063 : Nat := 1637927216642240704775

theorem tailTrace_43063 : CollatzResearch.WordTrace tailWord_43063 prefixEnd_43063 1637927216642240704775 := by
  unfold tailWord_43063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570636642997580419981843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1047091095331720279987895 1570636642997580419981843)
  ·
    refine ⟨2355954964496370629972765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1570636642997580419981843 2355954964496370629972765)
    ·
      refine ⟨883483111686138986239787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2355954964496370629972765 883483111686138986239787)
      ·
        refine ⟨1325224667529208479359681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883483111686138986239787 1325224667529208479359681)
        ·
          refine ⟨993918500646906359519761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1325224667529208479359681 993918500646906359519761)
          ·
            refine ⟨745438875485179769639821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 993918500646906359519761 745438875485179769639821)
            ·
              refine ⟨279539578306942413614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745438875485179769639821 279539578306942413614933)
              ·
                refine ⟨1637927216642240704775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 279539578306942413614933 1637927216642240704775)
                ·
                  rfl

theorem cell22_43063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 9].length) (baseStart_43063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43063 prefixEnd_43063 := by exact prefixLift 43063
  have htrace : WordTrace (prefixWord ++ tailWord_43063) baseStart_43063 baseEnd_43063 := by
    simpa [prefixWord, tailWord_43063, baseEnd_43063] using wordTrace_append hprefix tailTrace_43063
  have hstable : (prefixWord ++ tailWord_43063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43063).length < 2 ^ (prefixWord ++ tailWord_43063).sum := by decide
  have hdescent : baseEnd_43063 < baseStart_43063 := by decide
  rcases family_descends (prefixWord ++ tailWord_43063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43101 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_43101 : Nat := 118140960795 + 43101 * 2 ^ 59
def prefixEnd_43101 : Nat := 4983230072969 + 3 ^ 40 * 43101 * 2
def baseEnd_43101 : Nat := 14754353126360733892859

theorem tailTrace_43101 : CollatzResearch.WordTrace tailWord_43101 prefixEnd_43101 14754353126360733892859 := by
  unfold tailWord_43101
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572022616859912909865157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1048015077906608606576771 1572022616859912909865157)
  ·
    refine ⟨294754240661233670599717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1572022616859912909865157 294754240661233670599717)
    ·
      refine ⟨55266420123981313237447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294754240661233670599717 55266420123981313237447)
      ·
        refine ⟨82899630185971969856171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55266420123981313237447 82899630185971969856171)
        ·
          refine ⟨124349445278957954784257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82899630185971969856171 124349445278957954784257)
          ·
            refine ⟨93262083959218466088193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124349445278957954784257 93262083959218466088193)
            ·
              refine ⟨69946562969413849566145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93262083959218466088193 69946562969413849566145)
              ·
                refine ⟨52459922227060387174609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69946562969413849566145 52459922227060387174609)
                ·
                  refine ⟨39344941670295290380957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52459922227060387174609 39344941670295290380957)
                  ·
                    refine ⟨14754353126360733892859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39344941670295290380957 14754353126360733892859)
                    ·
                      rfl

theorem cell22_43101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_43101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43101 prefixEnd_43101 := by exact prefixLift 43101
  have htrace : WordTrace (prefixWord ++ tailWord_43101) baseStart_43101 baseEnd_43101 := by
    simpa [prefixWord, tailWord_43101, baseEnd_43101] using wordTrace_append hprefix tailTrace_43101
  have hstable : (prefixWord ++ tailWord_43101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43101).length < 2 ^ (prefixWord ++ tailWord_43101).sum := by decide
  have hdescent : baseEnd_43101 < baseStart_43101 := by decide
  rcases family_descends (prefixWord ++ tailWord_43101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43114 : List Nat := [3, 1, 3, 2, 4, 1, 1, 7]
def baseStart_43114 : Nat := 118140960795 + 43114 * 2 ^ 59
def prefixEnd_43114 : Nat := 4983230072969 + 3 ^ 40 * 43114 * 2
def baseEnd_43114 : Nat := 1639867032448114813091

theorem tailTrace_43114 : CollatzResearch.WordTrace tailWord_43114 prefixEnd_43114 1639867032448114813091 := by
  unfold tailWord_43114
  simp only [CollatzResearch.WordTrace]
  refine ⟨393124191453204032522099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1048331177208544086725597 393124191453204032522099)
  ·
    refine ⟨589686287179806048783149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393124191453204032522099 589686287179806048783149)
    ·
      refine ⟨221132357692427268293681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 589686287179806048783149 221132357692427268293681)
      ·
        refine ⟨165849268269320451220261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221132357692427268293681 165849268269320451220261)
        ·
          refine ⟨31096737800497584603799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165849268269320451220261 31096737800497584603799)
          ·
            refine ⟨46645106700746376905699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31096737800497584603799 46645106700746376905699)
            ·
              refine ⟨69967660051119565358549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46645106700746376905699 69967660051119565358549)
              ·
                refine ⟨1639867032448114813091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69967660051119565358549 1639867032448114813091)
                ·
                  rfl

theorem cell22_43114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_43114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43114 prefixEnd_43114 := by exact prefixLift 43114
  have htrace : WordTrace (prefixWord ++ tailWord_43114) baseStart_43114 baseEnd_43114 := by
    simpa [prefixWord, tailWord_43114, baseEnd_43114] using wordTrace_append hprefix tailTrace_43114
  have hstable : (prefixWord ++ tailWord_43114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43114).length < 2 ^ (prefixWord ++ tailWord_43114).sum := by decide
  have hdescent : baseEnd_43114 < baseStart_43114 := by decide
  rcases family_descends (prefixWord ++ tailWord_43114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43140 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_43140 : Nat := 118140960795 + 43140 * 2 ^ 59
def prefixEnd_43140 : Nat := 4983230072969 + 3 ^ 40 * 43140 * 2
def baseEnd_43140 : Nat := 14767703623377632167739

theorem tailTrace_43140 : CollatzResearch.WordTrace tailWord_43140 prefixEnd_43140 14767703623377632167739 := by
  unfold tailWord_43140
  simp only [CollatzResearch.WordTrace]
  refine ⟨786722531859311285267437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1048963375812415047023249 786722531859311285267437)
  ·
    refine ⟨295020949447241731975289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 786722531859311285267437 295020949447241731975289)
    ·
      refine ⟨221265712085431298981467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295020949447241731975289 221265712085431298981467)
      ·
        refine ⟨331898568128146948472201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221265712085431298981467 331898568128146948472201)
        ·
          refine ⟨248923926096110211354151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331898568128146948472201 248923926096110211354151)
          ·
            refine ⟨373385889144165317031227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248923926096110211354151 373385889144165317031227)
            ·
              refine ⟨560078833716247975546841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373385889144165317031227 560078833716247975546841)
              ·
                refine ⟨420059125287185981660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560078833716247975546841 420059125287185981660131)
                ·
                  refine ⟨630088687930778972490197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420059125287185981660131 630088687930778972490197)
                  ·
                    refine ⟨14767703623377632167739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 630088687930778972490197 14767703623377632167739)
                    ·
                      rfl

theorem cell22_43140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_43140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43140 prefixEnd_43140 := by exact prefixLift 43140
  have htrace : WordTrace (prefixWord ++ tailWord_43140) baseStart_43140 baseEnd_43140 := by
    simpa [prefixWord, tailWord_43140, baseEnd_43140] using wordTrace_append hprefix tailTrace_43140
  have hstable : (prefixWord ++ tailWord_43140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43140).length < 2 ^ (prefixWord ++ tailWord_43140).sum := by decide
  have hdescent : baseEnd_43140 < baseStart_43140 := by decide
  rcases family_descends (prefixWord ++ tailWord_43140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43146 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_43146 : Nat := 118140960795 + 43146 * 2 ^ 59
def prefixEnd_43146 : Nat := 4983230072969 + 3 ^ 40 * 43146 * 2
def baseEnd_43146 : Nat := 14769757545995616517721

theorem tailTrace_43146 : CollatzResearch.WordTrace tailWord_43146 prefixEnd_43146 14769757545995616517721 := by
  unfold tailWord_43146
  simp only [CollatzResearch.WordTrace]
  refine ⟨393415975424221398813323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1049109267797923730168861 393415975424221398813323)
  ·
    refine ⟨590123963136332098219985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393415975424221398813323 590123963136332098219985)
    ·
      refine ⟨442592972352249073664989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590123963136332098219985 442592972352249073664989)
      ·
        refine ⟨165972364632093402624371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442592972352249073664989 165972364632093402624371)
        ·
          refine ⟨248958546948140103936557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165972364632093402624371 248958546948140103936557)
          ·
            refine ⟨93359455105552538976209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248958546948140103936557 93359455105552538976209)
            ·
              refine ⟨70019591329164404232157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93359455105552538976209 70019591329164404232157)
              ·
                refine ⟨26257346748436651587059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70019591329164404232157 26257346748436651587059)
                ·
                  refine ⟨39386020122654977380589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26257346748436651587059 39386020122654977380589)
                  ·
                    refine ⟨14769757545995616517721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39386020122654977380589 14769757545995616517721)
                    ·
                      rfl

theorem cell22_43146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_43146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43146 prefixEnd_43146 := by exact prefixLift 43146
  have htrace : WordTrace (prefixWord ++ tailWord_43146) baseStart_43146 baseEnd_43146 := by
    simpa [prefixWord, tailWord_43146, baseEnd_43146] using wordTrace_append hprefix tailTrace_43146
  have hstable : (prefixWord ++ tailWord_43146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43146).length < 2 ^ (prefixWord ++ tailWord_43146).sum := by decide
  have hdescent : baseEnd_43146 < baseStart_43146 := by decide
  rcases family_descends (prefixWord ++ tailWord_43146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43159 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 5]
def baseStart_43159 : Nat := 118140960795 + 43159 * 2 ^ 59
def prefixEnd_43159 : Nat := 4983230072969 + 3 ^ 40 * 43159 * 2
def baseEnd_43159 : Nat := 4924735903889305314227

theorem tailTrace_43159 : CollatzResearch.WordTrace tailWord_43159 prefixEnd_43159 4924735903889305314227 := by
  unfold tailWord_43159
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574138050649788815476531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1049425367099859210317687 1574138050649788815476531)
  ·
    refine ⟨2361207075974683223214797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574138050649788815476531 2361207075974683223214797)
    ·
      refine ⟨885452653490506208705549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2361207075974683223214797 885452653490506208705549)
      ·
        refine ⟨332044745058939828264581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 885452653490506208705549 332044745058939828264581)
        ·
          refine ⟨62258389698551217799609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332044745058939828264581 62258389698551217799609)
          ·
            refine ⟨46693792273913413349707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62258389698551217799609 46693792273913413349707)
            ·
              refine ⟨70040688410870120024561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46693792273913413349707 70040688410870120024561)
              ·
                refine ⟨52530516308152590018421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70040688410870120024561 52530516308152590018421)
                ·
                  refine ⟨4924735903889305314227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52530516308152590018421 4924735903889305314227)
                  ·
                    rfl

theorem cell22_43159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 5].length) (baseStart_43159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43159 prefixEnd_43159 := by exact prefixLift 43159
  have htrace : WordTrace (prefixWord ++ tailWord_43159) baseStart_43159 baseEnd_43159 := by
    simpa [prefixWord, tailWord_43159, baseEnd_43159] using wordTrace_append hprefix tailTrace_43159
  have hstable : (prefixWord ++ tailWord_43159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43159).length < 2 ^ (prefixWord ++ tailWord_43159).sum := by decide
  have hdescent : baseEnd_43159 < baseStart_43159 := by decide
  rcases family_descends (prefixWord ++ tailWord_43159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43221 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 6]
def baseStart_43221 : Nat := 118140960795 + 43221 * 2 ^ 59
def prefixEnd_43221 : Nat := 4983230072969 + 3 ^ 40 * 43221 * 2
def baseEnd_43221 : Nat := 4931810526240140297497

theorem tailTrace_43221 : CollatzResearch.WordTrace tailWord_43221 prefixEnd_43221 4931810526240140297497 := by
  unfold tailWord_43221
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576399376425173404233517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1050932917616782269489011 1576399376425173404233517)
  ·
    refine ⟨591149766159440026587569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1576399376425173404233517 591149766159440026587569)
    ·
      refine ⟨443362324619580019940677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591149766159440026587569 443362324619580019940677)
      ·
        refine ⟨83130435866171253738877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 443362324619580019940677 83130435866171253738877)
        ·
          refine ⟨31173913449814220152079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83130435866171253738877 31173913449814220152079)
          ·
            refine ⟨46760870174721330228119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31173913449814220152079 46760870174721330228119)
            ·
              refine ⟨70141305262081995342179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46760870174721330228119 70141305262081995342179)
              ·
                refine ⟨105211957893122993013269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70141305262081995342179 105211957893122993013269)
                ·
                  refine ⟨4931810526240140297497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105211957893122993013269 4931810526240140297497)
                  ·
                    rfl

theorem cell22_43221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_43221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43221 prefixEnd_43221 := by exact prefixLift 43221
  have htrace : WordTrace (prefixWord ++ tailWord_43221) baseStart_43221 baseEnd_43221 := by
    simpa [prefixWord, tailWord_43221, baseEnd_43221] using wordTrace_append hprefix tailTrace_43221
  have hstable : (prefixWord ++ tailWord_43221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43221).length < 2 ^ (prefixWord ++ tailWord_43221).sum := by decide
  have hdescent : baseEnd_43221 < baseStart_43221 := by decide
  rcases family_descends (prefixWord ++ tailWord_43221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43281 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 1, 3]
def baseStart_43281 : Nat := 118140960795 + 43281 * 2 ^ 59
def prefixEnd_43281 : Nat := 4983230072969 + 3 ^ 40 * 43281 * 2
def baseEnd_43281 : Nat := 14815970804900264392307

theorem tailTrace_43281 : CollatzResearch.WordTrace tailWord_43281 prefixEnd_43281 14815970804900264392307 := by
  unfold tailWord_43281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578587756207803651417697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1052391837471869100945131 1578587756207803651417697)
  ·
    refine ⟨1183940817155852738563273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1578587756207803651417697 1183940817155852738563273)
    ·
      refine ⟨887955612866889553922455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1183940817155852738563273 887955612866889553922455)
      ·
        refine ⟨1331933419300334330883683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887955612866889553922455 1331933419300334330883683)
        ·
          refine ⟨1997900128950501496325525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331933419300334330883683 1997900128950501496325525)
          ·
            refine ⟨93651568544554757640259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1997900128950501496325525 93651568544554757640259)
            ·
              refine ⟨140477352816832136460389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93651568544554757640259 140477352816832136460389)
              ·
                refine ⟨26339503653156025586323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140477352816832136460389 26339503653156025586323)
                ·
                  refine ⟨39509255479734038379485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26339503653156025586323 39509255479734038379485)
                  ·
                    refine ⟨14815970804900264392307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39509255479734038379485 14815970804900264392307)
                    ·
                      rfl

theorem cell22_43281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_43281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43281 prefixEnd_43281 := by exact prefixLift 43281
  have htrace : WordTrace (prefixWord ++ tailWord_43281) baseStart_43281 baseEnd_43281 := by
    simpa [prefixWord, tailWord_43281, baseEnd_43281] using wordTrace_append hprefix tailTrace_43281
  have hstable : (prefixWord ++ tailWord_43281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43281).length < 2 ^ (prefixWord ++ tailWord_43281).sum := by decide
  have hdescent : baseEnd_43281 < baseStart_43281 := by decide
  rcases family_descends (prefixWord ++ tailWord_43281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43324 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_43324 : Nat := 118140960795 + 43324 * 2 ^ 59
def prefixEnd_43324 : Nat := 4983230072969 + 3 ^ 40 * 43324 * 2
def baseEnd_43324 : Nat := 14830690583662485567175

theorem tailTrace_43324 : CollatzResearch.WordTrace tailWord_43324 prefixEnd_43324 14830690583662485567175 := by
  unfold tailWord_43324
  simp only [CollatzResearch.WordTrace]
  refine ⟨790078047526010997616513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1053437396701347996822017 790078047526010997616513)
  ·
    refine ⟨592558535644508248212385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 790078047526010997616513 592558535644508248212385)
    ·
      refine ⟨444418901733381186159289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 592558535644508248212385 444418901733381186159289)
      ·
        refine ⟨333314176300035889619467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444418901733381186159289 333314176300035889619467)
        ·
          refine ⟨499971264450053834429201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333314176300035889619467 499971264450053834429201)
          ·
            refine ⟨374978448337540375821901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499971264450053834429201 374978448337540375821901)
            ·
              refine ⟨140616918126577640933213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374978448337540375821901 140616918126577640933213)
              ·
                refine ⟨52731344297466615349955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140616918126577640933213 52731344297466615349955)
                ·
                  refine ⟨79097016446199923024933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52731344297466615349955 79097016446199923024933)
                  ·
                    refine ⟨14830690583662485567175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79097016446199923024933 14830690583662485567175)
                    ·
                      rfl

theorem cell22_43324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_43324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43324 prefixEnd_43324 := by exact prefixLift 43324
  have htrace : WordTrace (prefixWord ++ tailWord_43324) baseStart_43324 baseEnd_43324 := by
    simpa [prefixWord, tailWord_43324, baseEnd_43324] using wordTrace_append hprefix tailTrace_43324
  have hstable : (prefixWord ++ tailWord_43324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43324).length < 2 ^ (prefixWord ++ tailWord_43324).sum := by decide
  have hdescent : baseEnd_43324 < baseStart_43324 := by decide
  rcases family_descends (prefixWord ++ tailWord_43324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43352 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_43352 : Nat := 118140960795 + 43352 * 2 ^ 59
def prefixEnd_43352 : Nat := 4983230072969 + 3 ^ 40 * 43352 * 2
def baseEnd_43352 : Nat := 14840275555879745867089

theorem tailTrace_43352 : CollatzResearch.WordTrace tailWord_43352 prefixEnd_43352 14840275555879745867089 := by
  unfold tailWord_43352
  simp only [CollatzResearch.WordTrace]
  refine ⟨790588669475291388626155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1054118225967055184834873 790588669475291388626155)
  ·
    refine ⟨1185883004212937082939233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 790588669475291388626155 1185883004212937082939233)
    ·
      refine ⟨889412253159702812204425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185883004212937082939233 889412253159702812204425)
      ·
        refine ⟨667059189869777109153319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889412253159702812204425 667059189869777109153319)
        ·
          refine ⟨1000588784804665663729979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667059189869777109153319 1000588784804665663729979)
          ·
            refine ⟨1500883177206998495594969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000588784804665663729979 1500883177206998495594969)
            ·
              refine ⟨1125662382905248871696227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500883177206998495594969 1125662382905248871696227)
              ·
                refine ⟨1688493574357873307544341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125662382905248871696227 1688493574357873307544341)
                ·
                  refine ⟨79148136298025311291141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1688493574357873307544341 79148136298025311291141)
                  ·
                    refine ⟨14840275555879745867089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79148136298025311291141 14840275555879745867089)
                    ·
                      rfl

theorem cell22_43352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_43352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43352 prefixEnd_43352 := by exact prefixLift 43352
  have htrace : WordTrace (prefixWord ++ tailWord_43352) baseStart_43352 baseEnd_43352 := by
    simpa [prefixWord, tailWord_43352, baseEnd_43352] using wordTrace_append hprefix tailTrace_43352
  have hstable : (prefixWord ++ tailWord_43352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43352).length < 2 ^ (prefixWord ++ tailWord_43352).sum := by decide
  have hdescent : baseEnd_43352 < baseStart_43352 := by decide
  rcases family_descends (prefixWord ++ tailWord_43352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43397 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_43397 : Nat := 118140960795 + 43397 * 2 ^ 59
def prefixEnd_43397 : Nat := 4983230072969 + 3 ^ 40 * 43397 * 2
def baseEnd_43397 : Nat := 14855679975514628491951

theorem tailTrace_43397 : CollatzResearch.WordTrace tailWord_43397 prefixEnd_43397 14855679975514628491951 := by
  unfold tailWord_43397
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582818623787555462640445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1055212415858370308426963 1582818623787555462640445)
  ·
    refine ⟨593556983920333298490167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1582818623787555462640445 593556983920333298490167)
    ·
      refine ⟨890335475880499947735251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593556983920333298490167 890335475880499947735251)
      ·
        refine ⟨1335503213820749921602877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890335475880499947735251 1335503213820749921602877)
        ·
          refine ⟨500813705182781220601079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1335503213820749921602877 500813705182781220601079)
          ·
            refine ⟨751220557774171830901619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500813705182781220601079 751220557774171830901619)
            ·
              refine ⟨1126830836661257746352429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751220557774171830901619 1126830836661257746352429)
              ·
                refine ⟨422561563747971654882161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126830836661257746352429 422561563747971654882161)
                ·
                  refine ⟨316921172810978741161621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422561563747971654882161 316921172810978741161621)
                  ·
                    refine ⟨14855679975514628491951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 316921172810978741161621 14855679975514628491951)
                    ·
                      rfl

theorem cell22_43397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_43397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43397 prefixEnd_43397 := by exact prefixLift 43397
  have htrace : WordTrace (prefixWord ++ tailWord_43397) baseStart_43397 baseEnd_43397 := by
    simpa [prefixWord, tailWord_43397, baseEnd_43397] using wordTrace_append hprefix tailTrace_43397
  have hstable : (prefixWord ++ tailWord_43397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43397).length < 2 ^ (prefixWord ++ tailWord_43397).sum := by decide
  have hdescent : baseEnd_43397 < baseStart_43397 := by decide
  rcases family_descends (prefixWord ++ tailWord_43397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43476 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_43476 : Nat := 118140960795 + 43476 * 2 ^ 59
def prefixEnd_43476 : Nat := 4983230072969 + 3 ^ 40 * 43476 * 2
def baseEnd_43476 : Nat := 14882723289984755766709

theorem tailTrace_43476 : CollatzResearch.WordTrace tailWord_43476 prefixEnd_43476 14882723289984755766709 := by
  unfold tailWord_43476
  simp only [CollatzResearch.WordTrace]
  refine ⟨792849995250675977383141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1057133327000901303177521 792849995250675977383141)
  ·
    refine ⟨148659374109501745759339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 792849995250675977383141 148659374109501745759339)
    ·
      refine ⟨222989061164252618639009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148659374109501745759339 222989061164252618639009)
      ·
        refine ⟨167241795873189463979257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222989061164252618639009 167241795873189463979257)
        ·
          refine ⟨125431346904892097984443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167241795873189463979257 125431346904892097984443)
          ·
            refine ⟨188147020357338146976665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125431346904892097984443 188147020357338146976665)
            ·
              refine ⟨141110265268003610232499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188147020357338146976665 141110265268003610232499)
              ·
                refine ⟨211665397902005415348749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141110265268003610232499 211665397902005415348749)
                ·
                  refine ⟨79374524213252030755781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211665397902005415348749 79374524213252030755781)
                  ·
                    refine ⟨14882723289984755766709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79374524213252030755781 14882723289984755766709)
                    ·
                      rfl

theorem cell22_43476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_43476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43476 prefixEnd_43476 := by exact prefixLift 43476
  have htrace : WordTrace (prefixWord ++ tailWord_43476) baseStart_43476 baseEnd_43476 := by
    simpa [prefixWord, tailWord_43476, baseEnd_43476] using wordTrace_append hprefix tailTrace_43476
  have hstable : (prefixWord ++ tailWord_43476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43476).length < 2 ^ (prefixWord ++ tailWord_43476).sum := by decide
  have hdescent : baseEnd_43476 < baseStart_43476 := by decide
  rcases family_descends (prefixWord ++ tailWord_43476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43489 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_43489 : Nat := 118140960795 + 43489 * 2 ^ 59
def prefixEnd_43489 : Nat := 4983230072969 + 3 ^ 40 * 43489 * 2
def baseEnd_43489 : Nat := 14887173455657055191669

theorem tailTrace_43489 : CollatzResearch.WordTrace tailWord_43489 prefixEnd_43489 14887173455657055191669 := by
  unfold tailWord_43489
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586174139454255174989521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1057449426302836783326347 1586174139454255174989521)
  ·
    refine ⟨1189630604590691381242141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1586174139454255174989521 1189630604590691381242141)
    ·
      refine ⟨446111476721509267965803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1189630604590691381242141 446111476721509267965803)
      ·
        refine ⟨669167215082263901948705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446111476721509267965803 669167215082263901948705)
        ·
          refine ⟨501875411311697926461529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669167215082263901948705 501875411311697926461529)
          ·
            refine ⟨376406558483773444846147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501875411311697926461529 376406558483773444846147)
            ·
              refine ⟨564609837725660167269221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376406558483773444846147 564609837725660167269221)
              ·
                refine ⟨105864344573561281362979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564609837725660167269221 105864344573561281362979)
                ·
                  refine ⟨158796516860341922044469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105864344573561281362979 158796516860341922044469)
                  ·
                    refine ⟨14887173455657055191669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158796516860341922044469 14887173455657055191669)
                    ·
                      rfl

theorem cell22_43489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_43489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43489 prefixEnd_43489 := by exact prefixLift 43489
  have htrace : WordTrace (prefixWord ++ tailWord_43489) baseStart_43489 baseEnd_43489 := by
    simpa [prefixWord, tailWord_43489, baseEnd_43489] using wordTrace_append hprefix tailTrace_43489
  have hstable : (prefixWord ++ tailWord_43489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43489).length < 2 ^ (prefixWord ++ tailWord_43489).sum := by decide
  have hdescent : baseEnd_43489 < baseStart_43489 := by decide
  rcases family_descends (prefixWord ++ tailWord_43489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43493 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_43493 : Nat := 118140960795 + 43493 * 2 ^ 59
def prefixEnd_43493 : Nat := 4983230072969 + 3 ^ 40 * 43493 * 2
def baseEnd_43493 : Nat := 14888542737402378091657

theorem tailTrace_43493 : CollatzResearch.WordTrace tailWord_43493 prefixEnd_43493 14888542737402378091657 := by
  unfold tailWord_43493
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586320031439763858135133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1057546687626509238756755 1586320031439763858135133)
  ·
    refine ⟨594870011789911446800675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1586320031439763858135133 594870011789911446800675)
    ·
      refine ⟨892305017684867170201013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594870011789911446800675 892305017684867170201013)
      ·
        refine ⟨83653595407956297206345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 892305017684867170201013 83653595407956297206345)
        ·
          refine ⟨62740196555967222904759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83653595407956297206345 62740196555967222904759)
          ·
            refine ⟨94110294833950834357139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62740196555967222904759 94110294833950834357139)
            ·
              refine ⟨141165442250926251535709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94110294833950834357139 141165442250926251535709)
              ·
                refine ⟨52937040844097344325891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141165442250926251535709 52937040844097344325891)
                ·
                  refine ⟨79405561266146016488837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52937040844097344325891 79405561266146016488837)
                  ·
                    refine ⟨14888542737402378091657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79405561266146016488837 14888542737402378091657)
                    ·
                      rfl

theorem cell22_43493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_43493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43493 prefixEnd_43493 := by exact prefixLift 43493
  have htrace : WordTrace (prefixWord ++ tailWord_43493) baseStart_43493 baseEnd_43493 := by
    simpa [prefixWord, tailWord_43493, baseEnd_43493] using wordTrace_append hprefix tailTrace_43493
  have hstable : (prefixWord ++ tailWord_43493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43493).length < 2 ^ (prefixWord ++ tailWord_43493).sum := by decide
  have hdescent : baseEnd_43493 < baseStart_43493 := by decide
  rcases family_descends (prefixWord ++ tailWord_43493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43504 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_43504 : Nat := 118140960795 + 43504 * 2 ^ 59
def prefixEnd_43504 : Nat := 4983230072969 + 3 ^ 40 * 43504 * 2
def baseEnd_43504 : Nat := 14892308262202016066623

theorem tailTrace_43504 : CollatzResearch.WordTrace tailWord_43504 prefixEnd_43504 14892308262202016066623 := by
  unfold tailWord_43504
  simp only [CollatzResearch.WordTrace]
  refine ⟨793360617199956368392783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1057814156266608491190377 793360617199956368392783)
  ·
    refine ⟨1190040925799934552589175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793360617199956368392783 1190040925799934552589175)
    ·
      refine ⟨1785061388699901828883763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190040925799934552589175 1785061388699901828883763)
      ·
        refine ⟨2677592083049852743325645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785061388699901828883763 2677592083049852743325645)
        ·
          refine ⟨1004097031143694778747117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2677592083049852743325645 1004097031143694778747117)
          ·
            refine ⟨376536386678885542030169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1004097031143694778747117 376536386678885542030169)
            ·
              refine ⟨282402290009164156522627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376536386678885542030169 282402290009164156522627)
              ·
                refine ⟨423603435013746234783941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282402290009164156522627 423603435013746234783941)
                ·
                  refine ⟨79425644065077419021989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423603435013746234783941 79425644065077419021989)
                  ·
                    refine ⟨14892308262202016066623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79425644065077419021989 14892308262202016066623)
                    ·
                      rfl

theorem cell22_43504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_43504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43504 prefixEnd_43504 := by exact prefixLift 43504
  have htrace : WordTrace (prefixWord ++ tailWord_43504) baseStart_43504 baseEnd_43504 := by
    simpa [prefixWord, tailWord_43504, baseEnd_43504] using wordTrace_append hprefix tailTrace_43504
  have hstable : (prefixWord ++ tailWord_43504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43504).length < 2 ^ (prefixWord ++ tailWord_43504).sum := by decide
  have hdescent : baseEnd_43504 < baseStart_43504 := by decide
  rcases family_descends (prefixWord ++ tailWord_43504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43523 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 2, 3]
def baseStart_43523 : Nat := 118140960795 + 43523 * 2 ^ 59
def prefixEnd_43523 : Nat := 4983230072969 + 3 ^ 40 * 43523 * 2
def baseEnd_43523 : Nat := 14898812350492299841565

theorem tailTrace_43523 : CollatzResearch.WordTrace tailWord_43523 prefixEnd_43523 14898812350492299841565 := by
  unfold tailWord_43523
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587414221331078981727223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1058276147554052654484815 1587414221331078981727223)
  ·
    refine ⟨2381121331996618472590835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587414221331078981727223 2381121331996618472590835)
    ·
      refine ⟨3571681997994927708886253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381121331996618472590835 3571681997994927708886253)
      ·
        refine ⟨1339380749248097890832345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3571681997994927708886253 1339380749248097890832345)
        ·
          refine ⟨1004535561936073418124259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339380749248097890832345 1004535561936073418124259)
          ·
            refine ⟨1506803342904110127186389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004535561936073418124259 1506803342904110127186389)
            ·
              refine ⟨35315703349315081105931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1506803342904110127186389 35315703349315081105931)
              ·
                refine ⟨52973555023972621658897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35315703349315081105931 52973555023972621658897)
                ·
                  refine ⟨39730166267979466244173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52973555023972621658897 39730166267979466244173)
                  ·
                    refine ⟨14898812350492299841565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39730166267979466244173 14898812350492299841565)
                    ·
                      rfl

theorem cell22_43523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 3].length) (baseStart_43523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43523 prefixEnd_43523 := by exact prefixLift 43523
  have htrace : WordTrace (prefixWord ++ tailWord_43523) baseStart_43523 baseEnd_43523 := by
    simpa [prefixWord, tailWord_43523, baseEnd_43523] using wordTrace_append hprefix tailTrace_43523
  have hstable : (prefixWord ++ tailWord_43523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43523).length < 2 ^ (prefixWord ++ tailWord_43523).sum := by decide
  have hdescent : baseEnd_43523 < baseStart_43523 := by decide
  rcases family_descends (prefixWord ++ tailWord_43523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43568 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 1, 3]
def baseStart_43568 : Nat := 118140960795 + 43568 * 2 ^ 59
def prefixEnd_43568 : Nat := 4983230072969 + 3 ^ 40 * 43568 * 2
def baseEnd_43568 : Nat := 14914216770127182466427

theorem tailTrace_43568 : CollatzResearch.WordTrace tailWord_43568 prefixEnd_43568 14914216770127182466427 := by
  unfold tailWord_43568
  simp only [CollatzResearch.WordTrace]
  refine ⟨794527753084025833557679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1059370337445367778076905 794527753084025833557679)
  ·
    refine ⟨1191791629626038750336519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 794527753084025833557679 1191791629626038750336519)
    ·
      refine ⟨1787687444439058125504779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191791629626038750336519 1787687444439058125504779)
      ·
        refine ⟨2681531166658587188257169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787687444439058125504779 2681531166658587188257169)
        ·
          refine ⟨2011148374993940391192877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2681531166658587188257169 2011148374993940391192877)
          ·
            refine ⟨754180640622727646697329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2011148374993940391192877 754180640622727646697329)
            ·
              refine ⟨565635480467045735022997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754180640622727646697329 565635480467045735022997)
              ·
                refine ⟨26514163146892768829203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 565635480467045735022997 26514163146892768829203)
                ·
                  refine ⟨39771244720339153243805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26514163146892768829203 39771244720339153243805)
                  ·
                    refine ⟨14914216770127182466427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39771244720339153243805 14914216770127182466427)
                    ·
                      rfl

theorem cell22_43568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_43568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43568 prefixEnd_43568 := by exact prefixLift 43568
  have htrace : WordTrace (prefixWord ++ tailWord_43568) baseStart_43568 baseEnd_43568 := by
    simpa [prefixWord, tailWord_43568, baseEnd_43568] using wordTrace_append hprefix tailTrace_43568
  have hstable : (prefixWord ++ tailWord_43568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43568).length < 2 ^ (prefixWord ++ tailWord_43568).sum := by decide
  have hdescent : baseEnd_43568 < baseStart_43568 := by decide
  rcases family_descends (prefixWord ++ tailWord_43568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43626 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_43626 : Nat := 118140960795 + 43626 * 2 ^ 59
def prefixEnd_43626 : Nat := 4983230072969 + 3 ^ 40 * 43626 * 2
def baseEnd_43626 : Nat := 4978023785144788172083

theorem tailTrace_43626 : CollatzResearch.WordTrace tailWord_43626 prefixEnd_43626 4978023785144788172083 := by
  unfold tailWord_43626
  simp only [CollatzResearch.WordTrace]
  refine ⟨397792734989481893181683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1060780626638618381817821 397792734989481893181683)
  ·
    refine ⟨596689102484222839772525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397792734989481893181683 596689102484222839772525)
    ·
      refine ⟨223758413431583564914697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 596689102484222839772525 223758413431583564914697)
      ·
        refine ⟨167818810073687673686023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223758413431583564914697 167818810073687673686023)
        ·
          refine ⟨251728215110531510529035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167818810073687673686023 251728215110531510529035)
          ·
            refine ⟨377592322665797265793553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251728215110531510529035 377592322665797265793553)
            ·
              refine ⟨283194241999347949345165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377592322665797265793553 283194241999347949345165)
              ·
                refine ⟨106197840749755481004437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283194241999347949345165 106197840749755481004437)
                ·
                  refine ⟨4978023785144788172083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106197840749755481004437 4978023785144788172083)
                  ·
                    rfl

theorem cell22_43626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_43626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43626 prefixEnd_43626 := by exact prefixLift 43626
  have htrace : WordTrace (prefixWord ++ tailWord_43626) baseStart_43626 baseEnd_43626 := by
    simpa [prefixWord, tailWord_43626, baseEnd_43626] using wordTrace_append hprefix tailTrace_43626
  have hstable : (prefixWord ++ tailWord_43626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43626).length < 2 ^ (prefixWord ++ tailWord_43626).sum := by decide
  have hdescent : baseEnd_43626 < baseStart_43626 := by decide
  rcases family_descends (prefixWord ++ tailWord_43626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43641 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_43641 : Nat := 118140960795 + 43641 * 2 ^ 59
def prefixEnd_43641 : Nat := 4983230072969 + 3 ^ 40 * 43641 * 2
def baseEnd_43641 : Nat := 14939206161979325391203

theorem tailTrace_43641 : CollatzResearch.WordTrace tailWord_43641 prefixEnd_43641 14939206161979325391203 := by
  unfold tailWord_43641
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591718034903585134522777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1061145356602390089681851 1591718034903585134522777)
  ·
    refine ⟨1193788526177688850892083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1591718034903585134522777 1193788526177688850892083)
    ·
      refine ⟨1790682789266533276338125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1193788526177688850892083 1790682789266533276338125)
      ·
        refine ⟨671506045974949978626797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1790682789266533276338125 671506045974949978626797)
        ·
          refine ⟨251814767240606241985049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671506045974949978626797 251814767240606241985049)
          ·
            refine ⟨188861075430454681488787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251814767240606241985049 188861075430454681488787)
            ·
              refine ⟨283291613145682022233181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188861075430454681488787 283291613145682022233181)
              ·
                refine ⟨106234354929630758337443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283291613145682022233181 106234354929630758337443)
                ·
                  refine ⟨159351532394446137506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106234354929630758337443 159351532394446137506165)
                  ·
                    refine ⟨14939206161979325391203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159351532394446137506165 14939206161979325391203)
                    ·
                      rfl

theorem cell22_43641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_43641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43641 prefixEnd_43641 := by exact prefixLift 43641
  have htrace : WordTrace (prefixWord ++ tailWord_43641) baseStart_43641 baseEnd_43641 := by
    simpa [prefixWord, tailWord_43641, baseEnd_43641] using wordTrace_append hprefix tailTrace_43641
  have hstable : (prefixWord ++ tailWord_43641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43641).length < 2 ^ (prefixWord ++ tailWord_43641).sum := by decide
  have hdescent : baseEnd_43641 < baseStart_43641 := by decide
  rcases family_descends (prefixWord ++ tailWord_43641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43737 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 1, 3]
def baseStart_43737 : Nat := 118140960795 + 43737 * 2 ^ 59
def prefixEnd_43737 : Nat := 4983230072969 + 3 ^ 40 * 43737 * 2
def baseEnd_43737 : Nat := 14972068923867074990909

theorem tailTrace_43737 : CollatzResearch.WordTrace tailWord_43737 prefixEnd_43737 14972068923867074990909 := by
  unfold tailWord_43737
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595219442555793530017465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1063479628370529020011643 1595219442555793530017465)
  ·
    refine ⟨1196414581916845147513099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1595219442555793530017465 1196414581916845147513099)
    ·
      refine ⟨1794621872875267721269649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196414581916845147513099 1794621872875267721269649)
      ·
        refine ⟨1345966404656450790952237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794621872875267721269649 1345966404656450790952237)
        ·
          refine ⟨504737401746169046607089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1345966404656450790952237 504737401746169046607089)
          ·
            refine ⟨378553051309626784955317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504737401746169046607089 378553051309626784955317)
            ·
              refine ⟨35489348560277511089561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 378553051309626784955317 35489348560277511089561)
              ·
                refine ⟨26617011420208133317171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35489348560277511089561 26617011420208133317171)
                ·
                  refine ⟨39925517130312199975757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26617011420208133317171 39925517130312199975757)
                  ·
                    refine ⟨14972068923867074990909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39925517130312199975757 14972068923867074990909)
                    ·
                      rfl

theorem cell22_43737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_43737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43737 prefixEnd_43737 := by exact prefixLift 43737
  have htrace : WordTrace (prefixWord ++ tailWord_43737) baseStart_43737 baseEnd_43737 := by
    simpa [prefixWord, tailWord_43737, baseEnd_43737] using wordTrace_append hprefix tailTrace_43737
  have hstable : (prefixWord ++ tailWord_43737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43737).length < 2 ^ (prefixWord ++ tailWord_43737).sum := by decide
  have hdescent : baseEnd_43737 < baseStart_43737 := by decide
  rcases family_descends (prefixWord ++ tailWord_43737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43761 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 8]
def baseStart_43761 : Nat := 118140960795 + 43761 * 2 ^ 59
def prefixEnd_43761 : Nat := 4983230072969 + 3 ^ 40 * 43761 * 2
def baseEnd_43761 : Nat := 4993428204779670796945

theorem tailTrace_43761 : CollatzResearch.WordTrace tailWord_43761 prefixEnd_43761 4993428204779670796945 := by
  unfold tailWord_43761
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596094794468845628891137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1064063196312563752594091 1596094794468845628891137)
  ·
    refine ⟨1197071095851634221668353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1596094794468845628891137 1197071095851634221668353)
    ·
      refine ⟨897803321888725666251265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197071095851634221668353 897803321888725666251265)
      ·
        refine ⟨673352491416544249688449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897803321888725666251265 673352491416544249688449)
        ·
          refine ⟨505014368562408187266337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673352491416544249688449 505014368562408187266337)
          ·
            refine ⟨378760776421806140449753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505014368562408187266337 378760776421806140449753)
            ·
              refine ⟨284070582316354605337315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378760776421806140449753 284070582316354605337315)
              ·
                refine ⟨426105873474531908005973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284070582316354605337315 426105873474531908005973)
                ·
                  refine ⟨4993428204779670796945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 426105873474531908005973 4993428204779670796945)
                  ·
                    rfl

theorem cell22_43761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_43761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43761 prefixEnd_43761 := by exact prefixLift 43761
  have htrace : WordTrace (prefixWord ++ tailWord_43761) baseStart_43761 baseEnd_43761 := by
    simpa [prefixWord, tailWord_43761, baseEnd_43761] using wordTrace_append hprefix tailTrace_43761
  have hstable : (prefixWord ++ tailWord_43761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43761).length < 2 ^ (prefixWord ++ tailWord_43761).sum := by decide
  have hdescent : baseEnd_43761 < baseStart_43761 := by decide
  rcases family_descends (prefixWord ++ tailWord_43761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43793 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_43793 : Nat := 118140960795 + 43793 * 2 ^ 59
def prefixEnd_43793 : Nat := 4983230072969 + 3 ^ 40 * 43793 * 2
def baseEnd_43793 : Nat := 14991238868301595590737

theorem tailTrace_43793 : CollatzResearch.WordTrace tailWord_43793 prefixEnd_43793 14991238868301595590737 := by
  unfold tailWord_43793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597261930352915094056033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1064841286901943396037355 1597261930352915094056033)
  ·
    refine ⟨1197946447764686320542025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1597261930352915094056033 1197946447764686320542025)
    ·
      refine ⟨898459835823514740406519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197946447764686320542025 898459835823514740406519)
      ·
        refine ⟨1347689753735272110609779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898459835823514740406519 1347689753735272110609779)
        ·
          refine ⟨2021534630602908165914669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347689753735272110609779 2021534630602908165914669)
          ·
            refine ⟨758075486476090562218001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2021534630602908165914669 758075486476090562218001)
            ·
              refine ⟨568556614857067921663501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758075486476090562218001 568556614857067921663501)
              ·
                refine ⟨213208730571400470623813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568556614857067921663501 213208730571400470623813)
                ·
                  refine ⟨39976636982137588241965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213208730571400470623813 39976636982137588241965)
                  ·
                    refine ⟨14991238868301595590737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39976636982137588241965 14991238868301595590737)
                    ·
                      rfl

theorem cell22_43793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_43793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43793 prefixEnd_43793 := by exact prefixLift 43793
  have htrace : WordTrace (prefixWord ++ tailWord_43793) baseStart_43793 baseEnd_43793 := by
    simpa [prefixWord, tailWord_43793, baseEnd_43793] using wordTrace_append hprefix tailTrace_43793
  have hstable : (prefixWord ++ tailWord_43793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43793).length < 2 ^ (prefixWord ++ tailWord_43793).sum := by decide
  have hdescent : baseEnd_43793 < baseStart_43793 := by decide
  rcases family_descends (prefixWord ++ tailWord_43793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43810 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_43810 : Nat := 118140960795 + 43810 * 2 ^ 59
def prefixEnd_43810 : Nat := 4983230072969 + 3 ^ 40 * 43810 * 2
def baseEnd_43810 : Nat := 14997058315719217915685

theorem tailTrace_43810 : CollatzResearch.WordTrace tailWord_43810 prefixEnd_43810 14997058315719217915685 := by
  unfold tailWord_43810
  simp only [CollatzResearch.WordTrace]
  refine ⟨399470492822831749356221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1065254647527551331616589 399470492822831749356221)
  ·
    refine ⟨149801434808561906008583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 399470492822831749356221 149801434808561906008583)
    ·
      refine ⟨224702152212842859012875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149801434808561906008583 224702152212842859012875)
      ·
        refine ⟨337053228319264288519313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224702152212842859012875 337053228319264288519313)
        ·
          refine ⟨252789921239448216389485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337053228319264288519313 252789921239448216389485)
          ·
            refine ⟨94796220464793081146057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252789921239448216389485 94796220464793081146057)
            ·
              refine ⟨71097165348594810859543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94796220464793081146057 71097165348594810859543)
              ·
                refine ⟨106645748022892216289315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71097165348594810859543 106645748022892216289315)
                ·
                  refine ⟨159968622034338324433973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106645748022892216289315 159968622034338324433973)
                  ·
                    refine ⟨14997058315719217915685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159968622034338324433973 14997058315719217915685)
                    ·
                      rfl

theorem cell22_43810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_43810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43810 prefixEnd_43810 := by exact prefixLift 43810
  have htrace : WordTrace (prefixWord ++ tailWord_43810) baseStart_43810 baseEnd_43810 := by
    simpa [prefixWord, tailWord_43810, baseEnd_43810] using wordTrace_append hprefix tailTrace_43810
  have hstable : (prefixWord ++ tailWord_43810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43810).length < 2 ^ (prefixWord ++ tailWord_43810).sum := by decide
  have hdescent : baseEnd_43810 < baseStart_43810 := by decide
  rcases family_descends (prefixWord ++ tailWord_43810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43844 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_43844 : Nat := 118140960795 + 43844 * 2 ^ 59
def prefixEnd_43844 : Nat := 4983230072969 + 3 ^ 40 * 43844 * 2
def baseEnd_43844 : Nat := 15008697210554462565581

theorem tailTrace_43844 : CollatzResearch.WordTrace tailWord_43844 prefixEnd_43844 15008697210554462565581 := by
  unfold tailWord_43844
  simp only [CollatzResearch.WordTrace]
  refine ⟨799561026584075402081293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1066081368778767202775057 799561026584075402081293)
  ·
    refine ⟨299835384969028275780485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 799561026584075402081293 299835384969028275780485)
    ·
      refine ⟨56219134681692801708841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299835384969028275780485 56219134681692801708841)
      ·
        refine ⟨42164351011269601281631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56219134681692801708841 42164351011269601281631)
        ·
          refine ⟨63246526516904401922447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42164351011269601281631 63246526516904401922447)
          ·
            refine ⟨94869789775356602883671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63246526516904401922447 94869789775356602883671)
            ·
              refine ⟨142304684663034904325507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94869789775356602883671 142304684663034904325507)
              ·
                refine ⟨213457026994552356488261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142304684663034904325507 213457026994552356488261)
                ·
                  refine ⟨40023192561478566841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213457026994552356488261 40023192561478566841549)
                  ·
                    refine ⟨15008697210554462565581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40023192561478566841549 15008697210554462565581)
                    ·
                      rfl

theorem cell22_43844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_43844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43844 prefixEnd_43844 := by exact prefixLift 43844
  have htrace : WordTrace (prefixWord ++ tailWord_43844) baseStart_43844 baseEnd_43844 := by
    simpa [prefixWord, tailWord_43844, baseEnd_43844] using wordTrace_append hprefix tailTrace_43844
  have hstable : (prefixWord ++ tailWord_43844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43844).length < 2 ^ (prefixWord ++ tailWord_43844).sum := by decide
  have hdescent : baseEnd_43844 < baseStart_43844 := by decide
  rcases family_descends (prefixWord ++ tailWord_43844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43874 : List Nat := [3, 3, 2, 1, 4, 1, 2, 6]
def baseStart_43874 : Nat := 118140960795 + 43874 * 2 ^ 59
def prefixEnd_43874 : Nat := 4983230072969 + 3 ^ 40 * 43874 * 2
def baseEnd_43874 : Nat := 1668774091516042701721

theorem tailTrace_43874 : CollatzResearch.WordTrace tailWord_43874 prefixEnd_43874 1668774091516042701721 := by
  unfold tailWord_43874
  simp only [CollatzResearch.WordTrace]
  refine ⟨400054060764866481938669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1066810828706310618503117 400054060764866481938669)
  ·
    refine ⟨150020272786824930727001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 400054060764866481938669 150020272786824930727001)
    ·
      refine ⟨112515204590118698045251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150020272786824930727001 112515204590118698045251)
      ·
        refine ⟨168772806885178047067877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112515204590118698045251 168772806885178047067877)
        ·
          refine ⟨31644901290970883825227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168772806885178047067877 31644901290970883825227)
          ·
            refine ⟨47467351936456325737841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31644901290970883825227 47467351936456325737841)
            ·
              refine ⟨35600513952342244303381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47467351936456325737841 35600513952342244303381)
              ·
                refine ⟨1668774091516042701721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35600513952342244303381 1668774091516042701721)
                ·
                  rfl

theorem cell22_43874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_43874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43874 prefixEnd_43874 := by exact prefixLift 43874
  have htrace : WordTrace (prefixWord ++ tailWord_43874) baseStart_43874 baseEnd_43874 := by
    simpa [prefixWord, tailWord_43874, baseEnd_43874] using wordTrace_append hprefix tailTrace_43874
  have hstable : (prefixWord ++ tailWord_43874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43874).length < 2 ^ (prefixWord ++ tailWord_43874).sum := by decide
  have hdescent : baseEnd_43874 < baseStart_43874 := by decide
  rcases family_descends (prefixWord ++ tailWord_43874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43889 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 1, 3]
def baseStart_43889 : Nat := 118140960795 + 43889 * 2 ^ 59
def prefixEnd_43889 : Nat := 4983230072969 + 3 ^ 40 * 43889 * 2
def baseEnd_43889 : Nat := 15024101630189345190443

theorem tailTrace_43889 : CollatzResearch.WordTrace tailWord_43889 prefixEnd_43889 15024101630189345190443 := by
  unfold tailWord_43889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600763338005123489550721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1067175558670082326367147 1600763338005123489550721)
  ·
    refine ⟨1200572503503842617163041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1600763338005123489550721 1200572503503842617163041)
    ·
      refine ⟨900429377627881962872281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1200572503503842617163041 900429377627881962872281)
      ·
        refine ⟨675322033220911472154211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900429377627881962872281 675322033220911472154211)
        ·
          refine ⟨1012983049831367208231317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675322033220911472154211 1012983049831367208231317)
          ·
            refine ⟨47483580460845337885843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1012983049831367208231317 47483580460845337885843)
            ·
              refine ⟨71225370691268006828765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47483580460845337885843 71225370691268006828765)
              ·
                refine ⟨26709514009225502560787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71225370691268006828765 26709514009225502560787)
                ·
                  refine ⟨40064271013838253841181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26709514009225502560787 40064271013838253841181)
                  ·
                    refine ⟨15024101630189345190443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40064271013838253841181 15024101630189345190443)
                    ·
                      rfl

theorem cell22_43889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_43889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43889 prefixEnd_43889 := by exact prefixLift 43889
  have htrace : WordTrace (prefixWord ++ tailWord_43889) baseStart_43889 baseEnd_43889 := by
    simpa [prefixWord, tailWord_43889, baseEnd_43889] using wordTrace_append hprefix tailTrace_43889
  have hstable : (prefixWord ++ tailWord_43889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43889).length < 2 ^ (prefixWord ++ tailWord_43889).sum := by decide
  have hdescent : baseEnd_43889 < baseStart_43889 := by decide
  rcases family_descends (prefixWord ++ tailWord_43889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43898 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_43898 : Nat := 118140960795 + 43898 * 2 ^ 59
def prefixEnd_43898 : Nat := 4983230072969 + 3 ^ 40 * 43898 * 2
def baseEnd_43898 : Nat := 15027182514116321715415

theorem tailTrace_43898 : CollatzResearch.WordTrace tailWord_43898 prefixEnd_43898 15027182514116321715415 := by
  unfold tailWord_43898
  simp only [CollatzResearch.WordTrace]
  refine ⟨400272898743129506657087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1067394396648345351085565 400272898743129506657087)
  ·
    refine ⟨600409348114694259985631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400272898743129506657087 600409348114694259985631)
    ·
      refine ⟨900614022172041389978447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600409348114694259985631 900614022172041389978447)
      ·
        refine ⟨1350921033258062084967671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900614022172041389978447 1350921033258062084967671)
        ·
          refine ⟨2026381549887093127451507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350921033258062084967671 2026381549887093127451507)
          ·
            refine ⟨3039572324830639691177261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026381549887093127451507 3039572324830639691177261)
            ·
              refine ⟨1139839621811489884191473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3039572324830639691177261 1139839621811489884191473)
              ·
                refine ⟨854879716358617413143605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139839621811489884191473 854879716358617413143605)
                ·
                  refine ⟨80144973408620382482213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854879716358617413143605 80144973408620382482213)
                  ·
                    refine ⟨15027182514116321715415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80144973408620382482213 15027182514116321715415)
                    ·
                      rfl

theorem cell22_43898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_43898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43898 prefixEnd_43898 := by exact prefixLift 43898
  have htrace : WordTrace (prefixWord ++ tailWord_43898) baseStart_43898 baseEnd_43898 := by
    simpa [prefixWord, tailWord_43898, baseEnd_43898] using wordTrace_append hprefix tailTrace_43898
  have hstable : (prefixWord ++ tailWord_43898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43898).length < 2 ^ (prefixWord ++ tailWord_43898).sum := by decide
  have hdescent : baseEnd_43898 < baseStart_43898 := by decide
  rcases family_descends (prefixWord ++ tailWord_43898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43932 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_43932 : Nat := 118140960795 + 43932 * 2 ^ 59
def prefixEnd_43932 : Nat := 4983230072969 + 3 ^ 40 * 43932 * 2
def baseEnd_43932 : Nat := 15038821408951566365311

theorem tailTrace_43932 : CollatzResearch.WordTrace tailWord_43932 prefixEnd_43932 15038821408951566365311 := by
  unfold tailWord_43932
  simp only [CollatzResearch.WordTrace]
  refine ⟨801165838424670916683025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1068221117899561222244033 801165838424670916683025)
  ·
    refine ⟨600874378818503187512269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 801165838424670916683025 600874378818503187512269)
    ·
      refine ⟨225327892056938695317101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 600874378818503187512269 225327892056938695317101)
      ·
        refine ⟨84497959521352010743913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225327892056938695317101 84497959521352010743913)
        ·
          refine ⟨63373469641014008057935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84497959521352010743913 63373469641014008057935)
          ·
            refine ⟨95060204461521012086903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63373469641014008057935 95060204461521012086903)
            ·
              refine ⟨142590306692281518130355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95060204461521012086903 142590306692281518130355)
              ·
                refine ⟨213885460038422277195533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142590306692281518130355 213885460038422277195533)
                ·
                  refine ⟨80207047514408353948325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213885460038422277195533 80207047514408353948325)
                  ·
                    refine ⟨15038821408951566365311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80207047514408353948325 15038821408951566365311)
                    ·
                      rfl

theorem cell22_43932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_43932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43932 prefixEnd_43932 := by exact prefixLift 43932
  have htrace : WordTrace (prefixWord ++ tailWord_43932) baseStart_43932 baseEnd_43932 := by
    simpa [prefixWord, tailWord_43932, baseEnd_43932] using wordTrace_append hprefix tailTrace_43932
  have hstable : (prefixWord ++ tailWord_43932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43932).length < 2 ^ (prefixWord ++ tailWord_43932).sum := by decide
  have hdescent : baseEnd_43932 < baseStart_43932 := by decide
  rcases family_descends (prefixWord ++ tailWord_43932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43960 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_43960 : Nat := 118140960795 + 43960 * 2 ^ 59
def prefixEnd_43960 : Nat := 4983230072969 + 3 ^ 40 * 43960 * 2
def baseEnd_43960 : Nat := 15048406381168826665225

theorem tailTrace_43960 : CollatzResearch.WordTrace tailWord_43960 prefixEnd_43960 15048406381168826665225 := by
  unfold tailWord_43960
  simp only [CollatzResearch.WordTrace]
  refine ⟨801676460373951307692667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1068901947165268410256889 801676460373951307692667)
  ·
    refine ⟨1202514690560926961539001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801676460373951307692667 1202514690560926961539001)
    ·
      refine ⟨901886017920695221154251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1202514690560926961539001 901886017920695221154251)
      ·
        refine ⟨1352829026881042831731377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901886017920695221154251 1352829026881042831731377)
        ·
          refine ⟨1014621770160782123798533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352829026881042831731377 1014621770160782123798533)
          ·
            refine ⟨190241581905146648212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1014621770160782123798533 190241581905146648212225)
            ·
              refine ⟨142681186428859986159169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190241581905146648212225 142681186428859986159169)
              ·
                refine ⟨107010889821644989619377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142681186428859986159169 107010889821644989619377)
                ·
                  refine ⟨80258167366233742214533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107010889821644989619377 80258167366233742214533)
                  ·
                    refine ⟨15048406381168826665225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80258167366233742214533 15048406381168826665225)
                    ·
                      rfl

theorem cell22_43960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_43960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43960 prefixEnd_43960 := by exact prefixLift 43960
  have htrace : WordTrace (prefixWord ++ tailWord_43960) baseStart_43960 baseEnd_43960 := by
    simpa [prefixWord, tailWord_43960, baseEnd_43960] using wordTrace_append hprefix tailTrace_43960
  have hstable : (prefixWord ++ tailWord_43960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43960).length < 2 ^ (prefixWord ++ tailWord_43960).sum := by decide
  have hdescent : baseEnd_43960 < baseStart_43960 := by decide
  rcases family_descends (prefixWord ++ tailWord_43960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43962 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_43962 : Nat := 118140960795 + 43962 * 2 ^ 59
def prefixEnd_43962 : Nat := 4983230072969 + 3 ^ 40 * 43962 * 2
def baseEnd_43962 : Nat := 15049091022041488115219

theorem tailTrace_43962 : CollatzResearch.WordTrace tailWord_43962 prefixEnd_43962 15049091022041488115219 := by
  unfold tailWord_43962
  simp only [CollatzResearch.WordTrace]
  refine ⟨400856466685164239239535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1068950577827104637972093 400856466685164239239535)
  ·
    refine ⟨601284700027746358859303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400856466685164239239535 601284700027746358859303)
    ·
      refine ⟨901927050041619538288955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601284700027746358859303 901927050041619538288955)
      ·
        refine ⟨1352890575062429307433433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901927050041619538288955 1352890575062429307433433)
        ·
          refine ⟨1014667931296821980575075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352890575062429307433433 1014667931296821980575075)
          ·
            refine ⟨1522001896945232970862613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014667931296821980575075 1522001896945232970862613)
            ·
              refine ⟨71343838919307795509185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1522001896945232970862613 71343838919307795509185)
              ·
                refine ⟨53507879189480846631889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71343838919307795509185 53507879189480846631889)
                ·
                  refine ⟨40130909392110634973917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53507879189480846631889 40130909392110634973917)
                  ·
                    refine ⟨15049091022041488115219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40130909392110634973917 15049091022041488115219)
                    ·
                      rfl

theorem cell22_43962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_43962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43962 prefixEnd_43962 := by exact prefixLift 43962
  have htrace : WordTrace (prefixWord ++ tailWord_43962) baseStart_43962 baseEnd_43962 := by
    simpa [prefixWord, tailWord_43962, baseEnd_43962] using wordTrace_append hprefix tailTrace_43962
  have hstable : (prefixWord ++ tailWord_43962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43962).length < 2 ^ (prefixWord ++ tailWord_43962).sum := by decide
  have hdescent : baseEnd_43962 < baseStart_43962 := by decide
  rcases family_descends (prefixWord ++ tailWord_43962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43981 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 6]
def baseStart_43981 : Nat := 118140960795 + 43981 * 2 ^ 59
def prefixEnd_43981 : Nat := 4983230072969 + 3 ^ 40 * 43981 * 2
def baseEnd_43981 : Nat := 5018531703443923963387

theorem tailTrace_43981 : CollatzResearch.WordTrace tailWord_43981 prefixEnd_43981 5018531703443923963387 := by
  unfold tailWord_43981
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604118853671823201899797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1069412569114548801266531 1604118853671823201899797)
  ·
    refine ⟨75193071265866712589053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1604118853671823201899797 75193071265866712589053)
    ·
      refine ⟨28197401724700017220895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75193071265866712589053 28197401724700017220895)
      ·
        refine ⟨42296102587050025831343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28197401724700017220895 42296102587050025831343)
        ·
          refine ⟨63444153880575038747015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42296102587050025831343 63444153880575038747015)
          ·
            refine ⟨95166230820862558120523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63444153880575038747015 95166230820862558120523)
            ·
              refine ⟨142749346231293837180785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95166230820862558120523 142749346231293837180785)
              ·
                refine ⟨107062009673470377885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142749346231293837180785 107062009673470377885589)
                ·
                  refine ⟨5018531703443923963387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107062009673470377885589 5018531703443923963387)
                  ·
                    rfl

theorem cell22_43981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_43981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_43981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_43981 prefixEnd_43981 := by exact prefixLift 43981
  have htrace : WordTrace (prefixWord ++ tailWord_43981) baseStart_43981 baseEnd_43981 := by
    simpa [prefixWord, tailWord_43981, baseEnd_43981] using wordTrace_append hprefix tailTrace_43981
  have hstable : (prefixWord ++ tailWord_43981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43981).length < 2 ^ (prefixWord ++ tailWord_43981).sum := by decide
  have hdescent : baseEnd_43981 < baseStart_43981 := by decide
  rcases family_descends (prefixWord ++ tailWord_43981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44037 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 5]
def baseStart_44037 : Nat := 118140960795 + 44037 * 2 ^ 59
def prefixEnd_44037 : Nat := 4983230072969 + 3 ^ 40 * 44037 * 2
def baseEnd_44037 : Nat := 5024921684922097496663

theorem tailTrace_44037 : CollatzResearch.WordTrace tailWord_44037 prefixEnd_44037 5024921684922097496663 := by
  unfold tailWord_44037
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606161341468944765938365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1070774227645963177292243 1606161341468944765938365)
  ·
    refine ⟨602310503050854287226887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1606161341468944765938365 602310503050854287226887)
    ·
      refine ⟨903465754576281430840331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602310503050854287226887 903465754576281430840331)
      ·
        refine ⟨1355198631864422146260497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903465754576281430840331 1355198631864422146260497)
        ·
          refine ⟨1016398973898316609695373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355198631864422146260497 1016398973898316609695373)
          ·
            refine ⟨381149615211868728635765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1016398973898316609695373 381149615211868728635765)
            ·
              refine ⟨35732776426112693309603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381149615211868728635765 35732776426112693309603)
              ·
                refine ⟨53599164639169039964405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35732776426112693309603 53599164639169039964405)
                ·
                  refine ⟨5024921684922097496663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53599164639169039964405 5024921684922097496663)
                  ·
                    rfl

theorem cell22_44037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_44037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44037 prefixEnd_44037 := by exact prefixLift 44037
  have htrace : WordTrace (prefixWord ++ tailWord_44037) baseStart_44037 baseEnd_44037 := by
    simpa [prefixWord, tailWord_44037, baseEnd_44037] using wordTrace_append hprefix tailTrace_44037
  have hstable : (prefixWord ++ tailWord_44037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44037).length < 2 ^ (prefixWord ++ tailWord_44037).sum := by decide
  have hdescent : baseEnd_44037 < baseStart_44037 := by decide
  rcases family_descends (prefixWord ++ tailWord_44037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44067 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 1, 4]
def baseStart_44067 : Nat := 118140960795 + 44067 * 2 ^ 59
def prefixEnd_44067 : Nat := 4983230072969 + 3 ^ 40 * 44067 * 2
def baseEnd_44067 : Nat := 15085034667856214239897

theorem tailTrace_44067 : CollatzResearch.WordTrace tailWord_44067 prefixEnd_44067 15085034667856214239897 := by
  unfold tailWord_44067
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607255531360259889530455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1071503687573506593020303 1607255531360259889530455)
  ·
    refine ⟨2410883297040389834295683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1607255531360259889530455 2410883297040389834295683)
    ·
      refine ⟨3616324945560584751443525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410883297040389834295683 3616324945560584751443525)
      ·
        refine ⟨678060927292609640895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3616324945560584751443525 678060927292609640895661)
        ·
          refine ⟨254272847734728615335873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 678060927292609640895661 254272847734728615335873)
          ·
            refine ⟨190704635801046461501905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254272847734728615335873 190704635801046461501905)
            ·
              refine ⟨143028476850784846126429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190704635801046461501905 143028476850784846126429)
              ·
                refine ⟨53635678819044317297411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143028476850784846126429 53635678819044317297411)
                ·
                  refine ⟨80453518228566475946117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53635678819044317297411 80453518228566475946117)
                  ·
                    refine ⟨15085034667856214239897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80453518228566475946117 15085034667856214239897)
                    ·
                      rfl

theorem cell22_44067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 4].length) (baseStart_44067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44067 prefixEnd_44067 := by exact prefixLift 44067
  have htrace : WordTrace (prefixWord ++ tailWord_44067) baseStart_44067 baseEnd_44067 := by
    simpa [prefixWord, tailWord_44067, baseEnd_44067] using wordTrace_append hprefix tailTrace_44067
  have hstable : (prefixWord ++ tailWord_44067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44067).length < 2 ^ (prefixWord ++ tailWord_44067).sum := by decide
  have hdescent : baseEnd_44067 < baseStart_44067 := by decide
  rcases family_descends (prefixWord ++ tailWord_44067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44095 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_44095 : Nat := 118140960795 + 44095 * 2 ^ 59
def prefixEnd_44095 : Nat := 4983230072969 + 3 ^ 40 * 44095 * 2
def baseEnd_44095 : Nat := 15094619640073474539811

theorem tailTrace_44095 : CollatzResearch.WordTrace tailWord_44095 prefixEnd_44095 15094619640073474539811 := by
  unfold tailWord_44095
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608276775258820671549739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1072184516839213781033159 1608276775258820671549739)
  ·
    refine ⟨2412415162888231007324609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1608276775258820671549739 2412415162888231007324609)
    ·
      refine ⟨1809311372166173255493457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2412415162888231007324609 1809311372166173255493457)
      ·
        refine ⟨1356983529124629941620093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1809311372166173255493457 1356983529124629941620093)
        ·
          refine ⟨508868823421736228107535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1356983529124629941620093 508868823421736228107535)
          ·
            refine ⟨763303235132604342161303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508868823421736228107535 763303235132604342161303)
            ·
              refine ⟨1144954852698906513241955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763303235132604342161303 1144954852698906513241955)
              ·
                refine ⟨1717432279048359769862933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144954852698906513241955 1717432279048359769862933)
                ·
                  refine ⟨80504638080391864212325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1717432279048359769862933 80504638080391864212325)
                  ·
                    refine ⟨15094619640073474539811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80504638080391864212325 15094619640073474539811)
                    ·
                      rfl

theorem cell22_44095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_44095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44095 prefixEnd_44095 := by exact prefixLift 44095
  have htrace : WordTrace (prefixWord ++ tailWord_44095) baseStart_44095 baseEnd_44095 := by
    simpa [prefixWord, tailWord_44095, baseEnd_44095] using wordTrace_append hprefix tailTrace_44095
  have hstable : (prefixWord ++ tailWord_44095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44095).length < 2 ^ (prefixWord ++ tailWord_44095).sum := by decide
  have hdescent : baseEnd_44095 < baseStart_44095 := by decide
  rcases family_descends (prefixWord ++ tailWord_44095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44110 : List Nat := [4, 1, 1, 1, 1, 3, 1, 10]
def baseStart_44110 : Nat := 118140960795 + 44110 * 2 ^ 59
def prefixEnd_44110 : Nat := 4983230072969 + 3 ^ 40 * 44110 * 2
def baseEnd_44110 : Nat := 1677750494068715046085

theorem tailTrace_44110 : CollatzResearch.WordTrace tailWord_44110 prefixEnd_44110 1677750494068715046085 := by
  unfold tailWord_44110
  simp only [CollatzResearch.WordTrace]
  refine ⟨201102983775559779168223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1072549246802985488897189 201102983775559779168223)
  ·
    refine ⟨301654475663339668752335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201102983775559779168223 301654475663339668752335)
    ·
      refine ⟨452481713495009503128503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301654475663339668752335 452481713495009503128503)
      ·
        refine ⟨678722570242514254692755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452481713495009503128503 678722570242514254692755)
        ·
          refine ⟨1018083855363771382039133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678722570242514254692755 1018083855363771382039133)
          ·
            refine ⟨381781445761414268264675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1018083855363771382039133 381781445761414268264675)
            ·
              refine ⟨572672168642121402397013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381781445761414268264675 572672168642121402397013)
              ·
                refine ⟨1677750494068715046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 572672168642121402397013 1677750494068715046085)
                ·
                  rfl

theorem cell22_44110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_44110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44110 prefixEnd_44110 := by exact prefixLift 44110
  have htrace : WordTrace (prefixWord ++ tailWord_44110) baseStart_44110 baseEnd_44110 := by
    simpa [prefixWord, tailWord_44110, baseEnd_44110] using wordTrace_append hprefix tailTrace_44110
  have hstable : (prefixWord ++ tailWord_44110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44110).length < 2 ^ (prefixWord ++ tailWord_44110).sum := by decide
  have hdescent : baseEnd_44110 < baseStart_44110 := by decide
  rcases family_descends (prefixWord ++ tailWord_44110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44140 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_44140 : Nat := 118140960795 + 44140 * 2 ^ 59
def prefixEnd_44140 : Nat := 4983230072969 + 3 ^ 40 * 44140 * 2
def baseEnd_44140 : Nat := 15110024059708357164673

theorem tailTrace_44140 : CollatzResearch.WordTrace tailWord_44140 prefixEnd_44140 15110024059708357164673 := by
  unfold tailWord_44140
  simp only [CollatzResearch.WordTrace]
  refine ⟨804959030047896678468937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1073278706730528904625249 804959030047896678468937)
  ·
    refine ⟨603719272535922508851703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 804959030047896678468937 603719272535922508851703)
    ·
      refine ⟨905578908803883763277555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603719272535922508851703 905578908803883763277555)
      ·
        refine ⟨1358368363205825644916333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905578908803883763277555 1358368363205825644916333)
        ·
          refine ⟨509388136202184616843625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1358368363205825644916333 509388136202184616843625)
          ·
            refine ⟨382041102151638462632719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509388136202184616843625 382041102151638462632719)
            ·
              refine ⟨573061653227457693949079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382041102151638462632719 573061653227457693949079)
              ·
                refine ⟨859592479841186540923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573061653227457693949079 859592479841186540923619)
                ·
                  refine ⟨1289388719761779811385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859592479841186540923619 1289388719761779811385429)
                  ·
                    refine ⟨15110024059708357164673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1289388719761779811385429 15110024059708357164673)
                    ·
                      rfl

theorem cell22_44140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_44140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44140 prefixEnd_44140 := by exact prefixLift 44140
  have htrace : WordTrace (prefixWord ++ tailWord_44140) baseStart_44140 baseEnd_44140 := by
    simpa [prefixWord, tailWord_44140, baseEnd_44140] using wordTrace_append hprefix tailTrace_44140
  have hstable : (prefixWord ++ tailWord_44140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44140).length < 2 ^ (prefixWord ++ tailWord_44140).sum := by decide
  have hdescent : baseEnd_44140 < baseStart_44140 := by decide
  rcases family_descends (prefixWord ++ tailWord_44140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44217 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 6]
def baseStart_44217 : Nat := 118140960795 + 44217 * 2 ^ 59
def prefixEnd_44217 : Nat := 4983230072969 + 3 ^ 40 * 44217 * 2
def baseEnd_44217 : Nat := 5045460911101940996479

theorem tailTrace_44217 : CollatzResearch.WordTrace tailWord_44217 prefixEnd_44217 5045460911101940996479 := by
  unfold tailWord_44217
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612726480816835507490905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075150987211223671660603 1612726480816835507490905)
  ·
    refine ⟨1209544860612626630618179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1612726480816835507490905 1209544860612626630618179)
    ·
      refine ⟨1814317290918939945927269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209544860612626630618179 1814317290918939945927269)
      ·
        refine ⟨340184492047301239861363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1814317290918939945927269 340184492047301239861363)
        ·
          refine ⟨510276738070951859792045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340184492047301239861363 510276738070951859792045)
          ·
            refine ⟨191353776776606947422017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 510276738070951859792045 191353776776606947422017)
            ·
              refine ⟨143515332582455210566513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191353776776606947422017 143515332582455210566513)
              ·
                refine ⟨107636499436841407924885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143515332582455210566513 107636499436841407924885)
                ·
                  refine ⟨5045460911101940996479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107636499436841407924885 5045460911101940996479)
                  ·
                    rfl

theorem cell22_44217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_44217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44217 prefixEnd_44217 := by exact prefixLift 44217
  have htrace : WordTrace (prefixWord ++ tailWord_44217) baseStart_44217 baseEnd_44217 := by
    simpa [prefixWord, tailWord_44217, baseEnd_44217] using wordTrace_append hprefix tailTrace_44217
  have hstable : (prefixWord ++ tailWord_44217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44217).length < 2 ^ (prefixWord ++ tailWord_44217).sum := by decide
  have hdescent : baseEnd_44217 < baseStart_44217 := by decide
  rcases family_descends (prefixWord ++ tailWord_44217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44232 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_44232 : Nat := 118140960795 + 44232 * 2 ^ 59
def prefixEnd_44232 : Nat := 4983230072969 + 3 ^ 40 * 44232 * 2
def baseEnd_44232 : Nat := 15141517539850783864391

theorem tailTrace_44232 : CollatzResearch.WordTrace tailWord_44232 prefixEnd_44232 15141517539850783864391 := by
  unfold tailWord_44232
  simp only [CollatzResearch.WordTrace]
  refine ⟨806636787881246534643475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1075515717174995379524633 806636787881246534643475)
  ·
    refine ⟨1209955181821869801965213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806636787881246534643475 1209955181821869801965213)
    ·
      refine ⟨453733193183201175736955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1209955181821869801965213 453733193183201175736955)
      ·
        refine ⟨680599789774801763605433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453733193183201175736955 680599789774801763605433)
        ·
          refine ⟨510449842331101322704075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680599789774801763605433 510449842331101322704075)
          ·
            refine ⟨765674763496651984056113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510449842331101322704075 765674763496651984056113)
            ·
              refine ⟨574256072622488988042085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765674763496651984056113 574256072622488988042085)
              ·
                refine ⟨107673013616716685257891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574256072622488988042085 107673013616716685257891)
                ·
                  refine ⟨161509520425075027886837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107673013616716685257891 161509520425075027886837)
                  ·
                    refine ⟨15141517539850783864391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161509520425075027886837 15141517539850783864391)
                    ·
                      rfl

theorem cell22_44232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_44232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44232 prefixEnd_44232 := by exact prefixLift 44232
  have htrace : WordTrace (prefixWord ++ tailWord_44232) baseStart_44232 baseEnd_44232 := by
    simpa [prefixWord, tailWord_44232, baseEnd_44232] using wordTrace_append hprefix tailTrace_44232
  have hstable : (prefixWord ++ tailWord_44232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44232).length < 2 ^ (prefixWord ++ tailWord_44232).sum := by decide
  have hdescent : baseEnd_44232 < baseStart_44232 := by decide
  rcases family_descends (prefixWord ++ tailWord_44232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44247 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_44247 : Nat := 118140960795 + 44247 * 2 ^ 59
def prefixEnd_44247 : Nat := 4983230072969 + 3 ^ 40 * 44247 * 2
def baseEnd_44247 : Nat := 15146652346395744739345

theorem tailTrace_44247 : CollatzResearch.WordTrace tailWord_44247 prefixEnd_44247 15146652346395744739345 := by
  unfold tailWord_44247
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613820670708150631082995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075880447138767087388663 1613820670708150631082995)
  ·
    refine ⟨2420731006062225946624493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1613820670708150631082995 2420731006062225946624493)
    ·
      refine ⟨907774127273334729984185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2420731006062225946624493 907774127273334729984185)
      ·
        refine ⟨680830595455001047488139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 907774127273334729984185 680830595455001047488139)
        ·
          refine ⟨1021245893182501571232209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680830595455001047488139 1021245893182501571232209)
          ·
            refine ⟨765934419886876178424157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1021245893182501571232209 765934419886876178424157)
            ·
              refine ⟨287225407457578566909059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 765934419886876178424157 287225407457578566909059)
              ·
                refine ⟨430838111186367850363589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287225407457578566909059 430838111186367850363589)
                ·
                  refine ⟨80782145847443971943173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430838111186367850363589 80782145847443971943173)
                  ·
                    refine ⟨15146652346395744739345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80782145847443971943173 15146652346395744739345)
                    ·
                      rfl

theorem cell22_44247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_44247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44247 prefixEnd_44247 := by exact prefixLift 44247
  have htrace : WordTrace (prefixWord ++ tailWord_44247) baseStart_44247 baseEnd_44247 := by
    simpa [prefixWord, tailWord_44247, baseEnd_44247] using wordTrace_append hprefix tailTrace_44247
  have hstable : (prefixWord ++ tailWord_44247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44247).length < 2 ^ (prefixWord ++ tailWord_44247).sum := by decide
  have hdescent : baseEnd_44247 < baseStart_44247 := by decide
  rcases family_descends (prefixWord ++ tailWord_44247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
