import V185TrunkScan23Chunk0114

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_679553 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_679553 : Nat := 118140960795 + 679553 * 2 ^ 59
def prefixEnd_679553 : Nat := 4983230072969 + 3 ^ 40 * 679553 * 2
def baseEnd_679553 : Nat := 348937319204884979462299

theorem tailTrace_679553 : CollatzResearch.WordTrace tailWord_679553 prefixEnd_679553 348937319204884979462299 := by
  unfold tailWord_679553
  simp only [CollatzResearch.WordTrace]
  refine ⟨24785334107103014257627313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16523556071402009505084875 24785334107103014257627313)
  ·
    refine ⟨18589000580327260693220485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24785334107103014257627313 18589000580327260693220485)
    ·
      refine ⟨3485437608811361379978841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18589000580327260693220485 3485437608811361379978841)
      ·
        refine ⟨2614078206608521034984131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3485437608811361379978841 2614078206608521034984131)
        ·
          refine ⟨3921117309912781552476197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614078206608521034984131 3921117309912781552476197)
          ·
            refine ⟨735209495608646541089287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3921117309912781552476197 735209495608646541089287)
            ·
              refine ⟨1102814243412969811633931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735209495608646541089287 1102814243412969811633931)
              ·
                refine ⟨1654221365119454717450897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102814243412969811633931 1654221365119454717450897)
                ·
                  refine ⟨1240666023839591038088173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654221365119454717450897 1240666023839591038088173)
                  ·
                    refine ⟨465249758939846639283065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240666023839591038088173 465249758939846639283065)
                    ·
                      refine ⟨348937319204884979462299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 465249758939846639283065 348937319204884979462299)
                      ·
                        rfl

theorem cell23_679553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_679553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679553 prefixEnd_679553 := by exact prefixLift 679553
  have htrace : WordTrace (prefixWord ++ tailWord_679553) baseStart_679553 baseEnd_679553 := by
    simpa [prefixWord, tailWord_679553, baseEnd_679553] using wordTrace_append hprefix tailTrace_679553
  have hstable : (prefixWord ++ tailWord_679553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679553).length < 2 ^ (prefixWord ++ tailWord_679553).sum := by decide
  have hdescent : baseEnd_679553 < baseStart_679553 := by decide
  rcases family_descends (prefixWord ++ tailWord_679553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679566 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_679566 : Nat := 118140960795 + 679566 * 2 ^ 59
def prefixEnd_679566 : Nat := 4983230072969 + 3 ^ 40 * 679566 * 2
def baseEnd_679566 : Nat := 348943994453393428599739

theorem tailTrace_679566 : CollatzResearch.WordTrace tailWord_679566 prefixEnd_679566 348943994453393428599739 := by
  unfold tailWord_679566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098226032006989684731319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16523872170703944985233701 3098226032006989684731319)
  ·
    refine ⟨4647339048010484527096979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3098226032006989684731319 4647339048010484527096979)
    ·
      refine ⟨6971008572015726790645469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647339048010484527096979 6971008572015726790645469)
      ·
        refine ⟨2614128214505897546492051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6971008572015726790645469 2614128214505897546492051)
        ·
          refine ⟨3921192321758846319738077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614128214505897546492051 3921192321758846319738077)
          ·
            refine ⟨1470447120659567369901779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3921192321758846319738077 1470447120659567369901779)
            ·
              refine ⟨2205670680989351054852669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470447120659567369901779 2205670680989351054852669)
              ·
                refine ⟨827126505371006645569751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205670680989351054852669 827126505371006645569751)
                ·
                  refine ⟨1240689758056509968354627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827126505371006645569751 1240689758056509968354627)
                  ·
                    refine ⟨1861034637084764952531941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240689758056509968354627 1861034637084764952531941)
                    ·
                      refine ⟨348943994453393428599739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1861034637084764952531941 348943994453393428599739)
                      ·
                        rfl

theorem cell23_679566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_679566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679566 prefixEnd_679566 := by exact prefixLift 679566
  have htrace : WordTrace (prefixWord ++ tailWord_679566) baseStart_679566 baseEnd_679566 := by
    simpa [prefixWord, tailWord_679566, baseEnd_679566] using wordTrace_append hprefix tailTrace_679566
  have hstable : (prefixWord ++ tailWord_679566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679566).length < 2 ^ (prefixWord ++ tailWord_679566).sum := by decide
  have hdescent : baseEnd_679566 < baseStart_679566 := by decide
  rcases family_descends (prefixWord ++ tailWord_679566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679576 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_679576 : Nat := 118140960795 + 679576 * 2 ^ 59
def prefixEnd_679576 : Nat := 4983230072969 + 3 ^ 40 * 679576 * 2
def baseEnd_679576 : Nat := 116316376419979463158231

theorem tailTrace_679576 : CollatzResearch.WordTrace tailWord_679576 prefixEnd_679576 116316376419979463158231 := by
  unfold tailWord_679576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393086493009844592857291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16524115324013126123809721 12393086493009844592857291)
  ·
    refine ⟨18589629739514766889285937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393086493009844592857291 18589629739514766889285937)
    ·
      refine ⟨13942222304636075166964453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18589629739514766889285937 13942222304636075166964453)
      ·
        refine ⟨2614166682119264093805835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13942222304636075166964453 2614166682119264093805835)
        ·
          refine ⟨3921250023178896140708753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614166682119264093805835 3921250023178896140708753)
          ·
            refine ⟨2940937517384172105531565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3921250023178896140708753 2940937517384172105531565)
            ·
              refine ⟨1102851569019064539574337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2940937517384172105531565 1102851569019064539574337)
              ·
                refine ⟨827138676764298404680753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102851569019064539574337 827138676764298404680753)
                ·
                  refine ⟨620354007573223803510565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827138676764298404680753 620354007573223803510565)
                  ·
                    refine ⟨116316376419979463158231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620354007573223803510565 116316376419979463158231)
                    ·
                      rfl

theorem cell23_679576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_679576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679576 prefixEnd_679576 := by exact prefixLift 679576
  have htrace : WordTrace (prefixWord ++ tailWord_679576) baseStart_679576 baseEnd_679576 := by
    simpa [prefixWord, tailWord_679576, baseEnd_679576] using wordTrace_append hprefix tailTrace_679576
  have hstable : (prefixWord ++ tailWord_679576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679576).length < 2 ^ (prefixWord ++ tailWord_679576).sum := by decide
  have hdescent : baseEnd_679576 < baseStart_679576 := by decide
  rcases family_descends (prefixWord ++ tailWord_679576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679602 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_679602 : Nat := 118140960795 + 679602 * 2 ^ 59
def prefixEnd_679602 : Nat := 4983230072969 + 3 ^ 40 * 679602 * 2
def baseEnd_679602 : Nat := 116320826585651762583191

theorem tailTrace_679602 : CollatzResearch.WordTrace tailWord_679602 prefixEnd_679602 116320826585651762583191 := by
  unfold tailWord_679602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196780320981373906540265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16524747522616997084107373 6196780320981373906540265)
  ·
    refine ⟨4647585240736030429905199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6196780320981373906540265 4647585240736030429905199)
    ·
      refine ⟨6971377861104045644857799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647585240736030429905199 6971377861104045644857799)
      ·
        refine ⟨10457066791656068467286699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971377861104045644857799 10457066791656068467286699)
        ·
          refine ⟨15685600187484102700930049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457066791656068467286699 15685600187484102700930049)
          ·
            refine ⟨11764200140613077025697537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15685600187484102700930049 11764200140613077025697537)
            ·
              refine ⟨8823150105459807769273153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11764200140613077025697537 8823150105459807769273153)
              ·
                refine ⟨6617362579094855826954865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823150105459807769273153 6617362579094855826954865)
                ·
                  refine ⟨4963021934321141870216149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6617362579094855826954865 4963021934321141870216149)
                  ·
                    refine ⟨116320826585651762583191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4963021934321141870216149 116320826585651762583191)
                    ·
                      rfl

theorem cell23_679602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_679602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679602 prefixEnd_679602 := by exact prefixLift 679602
  have htrace : WordTrace (prefixWord ++ tailWord_679602) baseStart_679602 baseEnd_679602 := by
    simpa [prefixWord, tailWord_679602, baseEnd_679602] using wordTrace_append hprefix tailTrace_679602
  have hstable : (prefixWord ++ tailWord_679602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679602).length < 2 ^ (prefixWord ++ tailWord_679602).sum := by decide
  have hdescent : baseEnd_679602 < baseStart_679602 := by decide
  rcases family_descends (prefixWord ++ tailWord_679602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679606 : List Nat := [5, 1, 3, 1, 1, 2, 1, 9]
def baseStart_679606 : Nat := 118140960795 + 679606 * 2 ^ 59
def prefixEnd_679606 : Nat := 4983230072969 + 3 ^ 40 * 679606 * 2
def baseEnd_679606 : Nat := 12924612358502713781465

theorem tailTrace_679606 : CollatzResearch.WordTrace tailWord_679606 prefixEnd_679606 12924612358502713781465 := by
  unfold tailWord_679606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549204198494437769331667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16524844783940669539537781 1549204198494437769331667)
  ·
    refine ⟨2323806297741656653997501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549204198494437769331667 2323806297741656653997501)
    ·
      refine ⟨871427361653121245249063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2323806297741656653997501 871427361653121245249063)
      ·
        refine ⟨1307141042479681867873595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871427361653121245249063 1307141042479681867873595)
        ·
          refine ⟨1960711563719522801810393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307141042479681867873595 1960711563719522801810393)
          ·
            refine ⟨1470533672789642101357795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1960711563719522801810393 1470533672789642101357795)
            ·
              refine ⟨2205800509184463152036693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470533672789642101357795 2205800509184463152036693)
              ·
                refine ⟨12924612358502713781465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2205800509184463152036693 12924612358502713781465)
                ·
                  rfl

theorem cell23_679606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_679606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679606 prefixEnd_679606 := by exact prefixLift 679606
  have htrace : WordTrace (prefixWord ++ tailWord_679606) baseStart_679606 baseEnd_679606 := by
    simpa [prefixWord, tailWord_679606, baseEnd_679606] using wordTrace_append hprefix tailTrace_679606
  have hstable : (prefixWord ++ tailWord_679606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679606).length < 2 ^ (prefixWord ++ tailWord_679606).sum := by decide
  have hdescent : baseEnd_679606 < baseStart_679606 := by decide
  rcases family_descends (prefixWord ++ tailWord_679606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679632 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_679632 : Nat := 118140960795 + 679632 * 2 ^ 59
def prefixEnd_679632 : Nat := 4983230072969 + 3 ^ 40 * 679632 * 2
def baseEnd_679632 : Nat := 116325961392196723458145

theorem tailTrace_679632 : CollatzResearch.WordTrace tailWord_679632 prefixEnd_679632 116325961392196723458145 := by
  unfold tailWord_679632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394107736908405374876575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16525476982544540499835433 12394107736908405374876575)
  ·
    refine ⟨18591161605362608062314863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12394107736908405374876575 18591161605362608062314863)
    ·
      refine ⟨27886742408043912093472295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18591161605362608062314863 27886742408043912093472295)
      ·
        refine ⟨41830113612065868140208443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27886742408043912093472295 41830113612065868140208443)
        ·
          refine ⟨62745170418098802210312665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41830113612065868140208443 62745170418098802210312665)
          ·
            refine ⟨47058877813574101657734499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62745170418098802210312665 47058877813574101657734499)
            ·
              refine ⟨70588316720361152486601749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47058877813574101657734499 70588316720361152486601749)
              ·
                refine ⟨3308827346266929022809457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70588316720361152486601749 3308827346266929022809457)
                ·
                  refine ⟨2481620509700196767107093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308827346266929022809457 2481620509700196767107093)
                  ·
                    refine ⟨116325961392196723458145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2481620509700196767107093 116325961392196723458145)
                    ·
                      rfl

theorem cell23_679632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_679632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679632 prefixEnd_679632 := by exact prefixLift 679632
  have htrace : WordTrace (prefixWord ++ tailWord_679632) baseStart_679632 baseEnd_679632 := by
    simpa [prefixWord, tailWord_679632, baseEnd_679632] using wordTrace_append hprefix tailTrace_679632
  have hstable : (prefixWord ++ tailWord_679632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679632).length < 2 ^ (prefixWord ++ tailWord_679632).sum := by decide
  have hdescent : baseEnd_679632 < baseStart_679632 := by decide
  rcases family_descends (prefixWord ++ tailWord_679632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679672 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_679672 : Nat := 118140960795 + 679672 * 2 ^ 59
def prefixEnd_679672 : Nat := 4983230072969 + 3 ^ 40 * 679672 * 2
def baseEnd_679672 : Nat := 348998423402770013874251

theorem tailTrace_679672 : CollatzResearch.WordTrace tailWord_679672 prefixEnd_679672 348998423402770013874251 := by
  unfold tailWord_679672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394837196835948790604635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16526449595781265054139513 12394837196835948790604635)
  ·
    refine ⟨18592255795253923185906953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12394837196835948790604635 18592255795253923185906953)
    ·
      refine ⟨13944191846440442389430215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18592255795253923185906953 13944191846440442389430215)
      ·
        refine ⟨20916287769660663584145323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13944191846440442389430215 20916287769660663584145323)
        ·
          refine ⟨31374431654490995376217985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20916287769660663584145323 31374431654490995376217985)
          ·
            refine ⟨23530823740868246532163489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31374431654490995376217985 23530823740868246532163489)
            ·
              refine ⟨17648117805651184899122617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23530823740868246532163489 17648117805651184899122617)
              ·
                refine ⟨13236088354238388674341963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17648117805651184899122617 13236088354238388674341963)
                ·
                  refine ⟨19854132531357583011512945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13236088354238388674341963 19854132531357583011512945)
                  ·
                    refine ⟨14890599398518187258634709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19854132531357583011512945 14890599398518187258634709)
                    ·
                      refine ⟨348998423402770013874251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14890599398518187258634709 348998423402770013874251)
                      ·
                        rfl

theorem cell23_679672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_679672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679672 prefixEnd_679672 := by exact prefixLift 679672
  have htrace : WordTrace (prefixWord ++ tailWord_679672) baseStart_679672 baseEnd_679672 := by
    simpa [prefixWord, tailWord_679672, baseEnd_679672] using wordTrace_append hprefix tailTrace_679672
  have hstable : (prefixWord ++ tailWord_679672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679672).length < 2 ^ (prefixWord ++ tailWord_679672).sum := by decide
  have hdescent : baseEnd_679672 < baseStart_679672 := by decide
  rcases family_descends (prefixWord ++ tailWord_679672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679689 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 3]
def baseStart_679689 : Nat := 118140960795 + 679689 * 2 ^ 59
def prefixEnd_679689 : Nat := 4983230072969 + 3 ^ 40 * 679689 * 2
def baseEnd_679689 : Nat := 349007152573896447361673

theorem tailTrace_679689 : CollatzResearch.WordTrace tailWord_679689 prefixEnd_679689 349007152573896447361673 := by
  unfold tailWord_679689
  simp only [CollatzResearch.WordTrace]
  refine ⟨24790294434610309484578121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16526862956406872989718747 24790294434610309484578121)
  ·
    refine ⟨18592720825957732113433591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24790294434610309484578121 18592720825957732113433591)
    ·
      refine ⟨27889081238936598170150387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18592720825957732113433591 27889081238936598170150387)
      ·
        refine ⟨41833621858404897255225581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27889081238936598170150387 41833621858404897255225581)
        ·
          refine ⟨15687608196901836470709593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41833621858404897255225581 15687608196901836470709593)
          ·
            refine ⟨11765706147676377353032195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15687608196901836470709593 11765706147676377353032195)
            ·
              refine ⟨17648559221514566029548293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11765706147676377353032195 17648559221514566029548293)
              ·
                refine ⟨3309104854033981130540305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17648559221514566029548293 3309104854033981130540305)
                ·
                  refine ⟨2481828640525485847905229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309104854033981130540305 2481828640525485847905229)
                  ·
                    refine ⟨930685740197057192964461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481828640525485847905229 930685740197057192964461)
                    ·
                      refine ⟨349007152573896447361673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930685740197057192964461 349007152573896447361673)
                      ·
                        rfl

theorem cell23_679689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_679689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679689 prefixEnd_679689 := by exact prefixLift 679689
  have htrace : WordTrace (prefixWord ++ tailWord_679689) baseStart_679689 baseEnd_679689 := by
    simpa [prefixWord, tailWord_679689, baseEnd_679689] using wordTrace_append hprefix tailTrace_679689
  have hstable : (prefixWord ++ tailWord_679689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679689).length < 2 ^ (prefixWord ++ tailWord_679689).sum := by decide
  have hdescent : baseEnd_679689 < baseStart_679689 := by decide
  rcases family_descends (prefixWord ++ tailWord_679689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679690 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_679690 : Nat := 118140960795 + 679690 * 2 ^ 59
def prefixEnd_679690 : Nat := 4983230072969 + 3 ^ 40 * 679690 * 2
def baseEnd_679690 : Nat := 349007666054550943449169

theorem tailTrace_679690 : CollatzResearch.WordTrace tailWord_679690 prefixEnd_679690 349007666054550943449169 := by
  unfold tailWord_679690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197582726901671663841131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16526887271737791103576349 6197582726901671663841131)
  ·
    refine ⟨9296374090352507495761697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6197582726901671663841131 9296374090352507495761697)
    ·
      refine ⟨6972280567764380621821273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9296374090352507495761697 6972280567764380621821273)
      ·
        refine ⟨5229210425823285466365955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6972280567764380621821273 5229210425823285466365955)
        ·
          refine ⟨7843815638734928199548933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229210425823285466365955 7843815638734928199548933)
          ·
            refine ⟨1470715432262799037415425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7843815638734928199548933 1470715432262799037415425)
            ·
              refine ⟨1103036574197099278061569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470715432262799037415425 1103036574197099278061569)
              ·
                refine ⟨827277430647824458546177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103036574197099278061569 827277430647824458546177)
                ·
                  refine ⟨620458072985868343909633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827277430647824458546177 620458072985868343909633)
                  ·
                    refine ⟨465343554739401257932225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 620458072985868343909633 465343554739401257932225)
                    ·
                      refine ⟨349007666054550943449169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 465343554739401257932225 349007666054550943449169)
                      ·
                        rfl

theorem cell23_679690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_679690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679690 prefixEnd_679690 := by exact prefixLift 679690
  have htrace : WordTrace (prefixWord ++ tailWord_679690) baseStart_679690 baseEnd_679690 := by
    simpa [prefixWord, tailWord_679690, baseEnd_679690] using wordTrace_append hprefix tailTrace_679690
  have hstable : (prefixWord ++ tailWord_679690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679690).length < 2 ^ (prefixWord ++ tailWord_679690).sum := by decide
  have hdescent : baseEnd_679690 < baseStart_679690 := by decide
  rcases family_descends (prefixWord ++ tailWord_679690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679700 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_679700 : Nat := 118140960795 + 679700 * 2 ^ 59
def prefixEnd_679700 : Nat := 4983230072969 + 3 ^ 40 * 679700 * 2
def baseEnd_679700 : Nat := 116337600287031968108041

theorem tailTrace_679700 : CollatzResearch.WordTrace tailWord_679700 prefixEnd_679700 116337600287031968108041 := by
  unfold tailWord_679700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12395347818785229181614277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16527130425046972242152369 12395347818785229181614277)
  ·
    refine ⟨2324127716022230471552677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12395347818785229181614277 2324127716022230471552677)
    ·
      refine ⟨435773946754168213416127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2324127716022230471552677 435773946754168213416127)
      ·
        refine ⟨653660920131252320124191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435773946754168213416127 653660920131252320124191)
        ·
          refine ⟨980491380196878480186287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653660920131252320124191 980491380196878480186287)
          ·
            refine ⟨1470737070295317720279431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980491380196878480186287 1470737070295317720279431)
            ·
              refine ⟨2206105605442976580419147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470737070295317720279431 2206105605442976580419147)
              ·
                refine ⟨3309158408164464870628721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206105605442976580419147 3309158408164464870628721)
                ·
                  refine ⟨2481868806123348652971541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309158408164464870628721 2481868806123348652971541)
                  ·
                    refine ⟨116337600287031968108041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2481868806123348652971541 116337600287031968108041)
                    ·
                      rfl

theorem cell23_679700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_679700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679700 prefixEnd_679700 := by exact prefixLift 679700
  have htrace : WordTrace (prefixWord ++ tailWord_679700) baseStart_679700 baseEnd_679700 := by
    simpa [prefixWord, tailWord_679700, baseEnd_679700] using wordTrace_append hprefix tailTrace_679700
  have hstable : (prefixWord ++ tailWord_679700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679700).length < 2 ^ (prefixWord ++ tailWord_679700).sum := by decide
  have hdescent : baseEnd_679700 < baseStart_679700 := by decide
  rcases family_descends (prefixWord ++ tailWord_679700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679706 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_679706 : Nat := 118140960795 + 679706 * 2 ^ 59
def prefixEnd_679706 : Nat := 4983230072969 + 3 ^ 40 * 679706 * 2
def baseEnd_679706 : Nat := 349015881745022880849095

theorem tailTrace_679706 : CollatzResearch.WordTrace tailWord_679706 prefixEnd_679706 349015881745022880849095 := by
  unfold tailWord_679706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197728618887180346986743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16527276317032480925297981 6197728618887180346986743)
  ·
    refine ⟨9296592928330770520480115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6197728618887180346986743 9296592928330770520480115)
    ·
      refine ⟨13944889392496155780720173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9296592928330770520480115 13944889392496155780720173)
      ·
        refine ⟨5229333522186058417770065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13944889392496155780720173 5229333522186058417770065)
        ·
          refine ⟨3922000141639543813327549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5229333522186058417770065 3922000141639543813327549)
          ·
            refine ⟨1470750053114828929997831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3922000141639543813327549 1470750053114828929997831)
            ·
              refine ⟨2206125079672243394996747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470750053114828929997831 2206125079672243394996747)
              ·
                refine ⟨3309187619508365092495121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206125079672243394996747 3309187619508365092495121)
                ·
                  refine ⟨2481890714631273819371341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309187619508365092495121 2481890714631273819371341)
                  ·
                    refine ⟨930709017986727682264253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481890714631273819371341 930709017986727682264253)
                    ·
                      refine ⟨349015881745022880849095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930709017986727682264253 349015881745022880849095)
                      ·
                        rfl

theorem cell23_679706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_679706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679706 prefixEnd_679706 := by exact prefixLift 679706
  have htrace : WordTrace (prefixWord ++ tailWord_679706) baseStart_679706 baseEnd_679706 := by
    simpa [prefixWord, tailWord_679706, baseEnd_679706] using wordTrace_append hprefix tailTrace_679706
  have hstable : (prefixWord ++ tailWord_679706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679706).length < 2 ^ (prefixWord ++ tailWord_679706).sum := by decide
  have hdescent : baseEnd_679706 < baseStart_679706 := by decide
  rcases family_descends (prefixWord ++ tailWord_679706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679799 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 7, 5]
def baseStart_679799 : Nat := 118140960795 + 679799 * 2 ^ 59
def prefixEnd_679799 : Nat := 4983230072969 + 3 ^ 40 * 679799 * 2
def baseEnd_679799 : Nat := 116354545148630338995389

theorem tailTrace_679799 : CollatzResearch.WordTrace tailWord_679799 prefixEnd_679799 116354545148630338995389 := by
  unfold tailWord_679799
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794306464211798271082451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16529537642807865514054967 24794306464211798271082451)
  ·
    refine ⟨37191459696317697406623677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24794306464211798271082451 37191459696317697406623677)
    ·
      refine ⟨13946797386119136527483879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37191459696317697406623677 13946797386119136527483879)
      ·
        refine ⟨20920196079178704791225819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13946797386119136527483879 20920196079178704791225819)
        ·
          refine ⟨31380294118768057186838729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20920196079178704791225819 31380294118768057186838729)
          ·
            refine ⟨23535220589076042890129047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31380294118768057186838729 23535220589076042890129047)
            ·
              refine ⟨35302830883614064335193571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23535220589076042890129047 35302830883614064335193571)
              ·
                refine ⟨52954246325421096502790357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35302830883614064335193571 52954246325421096502790357)
                ·
                  refine ⟨1241115148252056949284149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52954246325421096502790357 1241115148252056949284149)
                  ·
                    refine ⟨116354545148630338995389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1241115148252056949284149 116354545148630338995389)
                    ·
                      rfl

theorem cell23_679799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_679799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679799 prefixEnd_679799 := by exact prefixLift 679799
  have htrace : WordTrace (prefixWord ++ tailWord_679799) baseStart_679799 baseEnd_679799 := by
    simpa [prefixWord, tailWord_679799, baseEnd_679799] using wordTrace_append hprefix tailTrace_679799
  have hstable : (prefixWord ++ tailWord_679799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679799).length < 2 ^ (prefixWord ++ tailWord_679799).sum := by decide
  have hdescent : baseEnd_679799 < baseStart_679799 := by decide
  rcases family_descends (prefixWord ++ tailWord_679799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679819 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_679819 : Nat := 118140960795 + 679819 * 2 ^ 59
def prefixEnd_679819 : Nat := 4983230072969 + 3 ^ 40 * 679819 * 2
def baseEnd_679819 : Nat := 349073905058980938736075

theorem tailTrace_679819 : CollatzResearch.WordTrace tailWord_679819 prefixEnd_679819 349073905058980938736075 := by
  unfold tailWord_679819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24795035924139341686810511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16530023949426227791207007 24795035924139341686810511)
  ·
    refine ⟨37192553886209012530215767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24795035924139341686810511 37192553886209012530215767)
    ·
      refine ⟨55788830829313518795323651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37192553886209012530215767 55788830829313518795323651)
      ·
        refine ⟨83683246243970278192985477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55788830829313518795323651 83683246243970278192985477)
        ·
          refine ⟨15690608670744427161184777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83683246243970278192985477 15690608670744427161184777)
          ·
            refine ⟨11767956503058320370888583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15690608670744427161184777 11767956503058320370888583)
            ·
              refine ⟨17651934754587480556332875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767956503058320370888583 17651934754587480556332875)
              ·
                refine ⟨26477902131881220834499313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17651934754587480556332875 26477902131881220834499313)
                ·
                  refine ⟨19858426598910915625874485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26477902131881220834499313 19858426598910915625874485)
                  ·
                    refine ⟨1861727493647898339925733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19858426598910915625874485 1861727493647898339925733)
                    ·
                      refine ⟨349073905058980938736075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1861727493647898339925733 349073905058980938736075)
                      ·
                        rfl

theorem cell23_679819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_679819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679819 prefixEnd_679819 := by exact prefixLift 679819
  have htrace : WordTrace (prefixWord ++ tailWord_679819) baseStart_679819 baseEnd_679819 := by
    simpa [prefixWord, tailWord_679819, baseEnd_679819] using wordTrace_append hprefix tailTrace_679819
  have hstable : (prefixWord ++ tailWord_679819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679819).length < 2 ^ (prefixWord ++ tailWord_679819).sum := by decide
  have hdescent : baseEnd_679819 < baseStart_679819 := by decide
  rcases family_descends (prefixWord ++ tailWord_679819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679849 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_679849 : Nat := 118140960795 + 679849 * 2 ^ 59
def prefixEnd_679849 : Nat := 4983230072969 + 3 ^ 40 * 679849 * 2
def baseEnd_679849 : Nat := 349089309478615821360937

theorem tailTrace_679849 : CollatzResearch.WordTrace tailWord_679849 prefixEnd_679849 349089309478615821360937 := by
  unfold tailWord_679849
  simp only [CollatzResearch.WordTrace]
  refine ⟨24796130114030656810402601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16530753409353771206935067 24796130114030656810402601)
  ·
    refine ⟨18597097585522992607801951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24796130114030656810402601 18597097585522992607801951)
    ·
      refine ⟨27895646378284488911702927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18597097585522992607801951 27895646378284488911702927)
      ·
        refine ⟨41843469567426733367554391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27895646378284488911702927 41843469567426733367554391)
        ·
          refine ⟨62765204351140100051331587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41843469567426733367554391 62765204351140100051331587)
          ·
            refine ⟨94147806526710150076997381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62765204351140100051331587 94147806526710150076997381)
            ·
              refine ⟨17652713723758153139437009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94147806526710150076997381 17652713723758153139437009)
              ·
                refine ⟨13239535292818614854577757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17652713723758153139437009 13239535292818614854577757)
                ·
                  refine ⟨4964825734806980570466659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13239535292818614854577757 4964825734806980570466659)
                  ·
                    refine ⟨7447238602210470855699989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964825734806980570466659 7447238602210470855699989)
                    ·
                      refine ⟨349089309478615821360937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7447238602210470855699989 349089309478615821360937)
                      ·
                        rfl

theorem cell23_679849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_679849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679849 prefixEnd_679849 := by exact prefixLift 679849
  have htrace : WordTrace (prefixWord ++ tailWord_679849) baseStart_679849 baseEnd_679849 := by
    simpa [prefixWord, tailWord_679849, baseEnd_679849] using wordTrace_append hprefix tailTrace_679849
  have hstable : (prefixWord ++ tailWord_679849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679849).length < 2 ^ (prefixWord ++ tailWord_679849).sum := by decide
  have hdescent : baseEnd_679849 < baseStart_679849 := by decide
  rcases family_descends (prefixWord ++ tailWord_679849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679893 : List Nat := [1, 3, 2, 3, 2, 2, 3, 7]
def baseStart_679893 : Nat := 118140960795 + 679893 * 2 ^ 59
def prefixEnd_679893 : Nat := 4983230072969 + 3 ^ 40 * 679893 * 2
def baseEnd_679893 : Nat := 12930070467681987007805

theorem tailTrace_679893 : CollatzResearch.WordTrace tailWord_679893 prefixEnd_679893 12930070467681987007805 := by
  unfold tailWord_679893
  simp only [CollatzResearch.WordTrace]
  refine ⟨24797734925871252325004333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16531823283914168216669555 24797734925871252325004333)
  ·
    refine ⟨9299150597201719621876625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24797734925871252325004333 9299150597201719621876625)
    ·
      refine ⟨6974362947901289716407469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9299150597201719621876625 6974362947901289716407469)
      ·
        refine ⟨2615386105462983643652801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6974362947901289716407469 2615386105462983643652801)
        ·
          refine ⟨1961539579097237732739601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615386105462983643652801 1961539579097237732739601)
          ·
            refine ⟨1471154684322928299554701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961539579097237732739601 1471154684322928299554701)
            ·
              refine ⟨551683006621098112333013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1471154684322928299554701 551683006621098112333013)
              ·
                refine ⟨12930070467681987007805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 551683006621098112333013 12930070467681987007805)
                ·
                  rfl

theorem cell23_679893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 7].length) (baseStart_679893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679893 prefixEnd_679893 := by exact prefixLift 679893
  have htrace : WordTrace (prefixWord ++ tailWord_679893) baseStart_679893 baseEnd_679893 := by
    simpa [prefixWord, tailWord_679893, baseEnd_679893] using wordTrace_append hprefix tailTrace_679893
  have hstable : (prefixWord ++ tailWord_679893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679893).length < 2 ^ (prefixWord ++ tailWord_679893).sum := by decide
  have hdescent : baseEnd_679893 < baseStart_679893 := by decide
  rcases family_descends (prefixWord ++ tailWord_679893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679903 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_679903 : Nat := 118140960795 + 679903 * 2 ^ 59
def prefixEnd_679903 : Nat := 4983230072969 + 3 ^ 40 * 679903 * 2
def baseEnd_679903 : Nat := 349117037433958610085689

theorem tailTrace_679903 : CollatzResearch.WordTrace tailWord_679903 prefixEnd_679903 349117037433958610085689 := by
  unfold tailWord_679903
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798099655835024032868363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16532066437223349355245575 24798099655835024032868363)
  ·
    refine ⟨37197149483752536049302545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24798099655835024032868363 37197149483752536049302545)
    ·
      refine ⟨27897862112814402036976909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37197149483752536049302545 27897862112814402036976909)
      ·
        refine ⟨10461698292305400763866341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27897862112814402036976909 10461698292305400763866341)
        ·
          refine ⟨1961568429807262643224939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10461698292305400763866341 1961568429807262643224939)
          ·
            refine ⟨2942352644710893964837409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961568429807262643224939 2942352644710893964837409)
            ·
              refine ⟨2206764483533170473628057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942352644710893964837409 2206764483533170473628057)
              ·
                refine ⟨1655073362649877855221043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206764483533170473628057 1655073362649877855221043)
                ·
                  refine ⟨2482610043974816782831565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655073362649877855221043 2482610043974816782831565)
                  ·
                    refine ⟨930978766490556293561837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482610043974816782831565 930978766490556293561837)
                    ·
                      refine ⟨349117037433958610085689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930978766490556293561837 349117037433958610085689)
                      ·
                        rfl

theorem cell23_679903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_679903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679903 prefixEnd_679903 := by exact prefixLift 679903
  have htrace : WordTrace (prefixWord ++ tailWord_679903) baseStart_679903 baseEnd_679903 := by
    simpa [prefixWord, tailWord_679903, baseEnd_679903] using wordTrace_append hprefix tailTrace_679903
  have hstable : (prefixWord ++ tailWord_679903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679903).length < 2 ^ (prefixWord ++ tailWord_679903).sum := by decide
  have hdescent : baseEnd_679903 < baseStart_679903 := by decide
  rcases family_descends (prefixWord ++ tailWord_679903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679907 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 1, 2, 3]
def baseStart_679907 : Nat := 118140960795 + 679907 * 2 ^ 59
def prefixEnd_679907 : Nat := 4983230072969 + 3 ^ 40 * 679907 * 2
def baseEnd_679907 : Nat := 349119091356576594435671

theorem tailTrace_679907 : CollatzResearch.WordTrace tailWord_679907 prefixEnd_679907 349119091356576594435671 := by
  unfold tailWord_679907
  simp only [CollatzResearch.WordTrace]
  refine ⟨24798245547820532716013975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16532163698547021810675983 24798245547820532716013975)
  ·
    refine ⟨37197368321730799074020963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24798245547820532716013975 37197368321730799074020963)
    ·
      refine ⟨55796052482596198611031445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37197368321730799074020963 55796052482596198611031445)
      ·
        refine ⟨2615439960121696809892099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55796052482596198611031445 2615439960121696809892099)
        ·
          refine ⟨3923159940182545214838149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2615439960121696809892099 3923159940182545214838149)
          ·
            refine ⟨735592488784227227782153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3923159940182545214838149 735592488784227227782153)
            ·
              refine ⟨551694366588170420836615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735592488784227227782153 551694366588170420836615)
              ·
                refine ⟨827541549882255631254923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551694366588170420836615 827541549882255631254923)
                ·
                  refine ⟨1241312324823383446882385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827541549882255631254923 1241312324823383446882385)
                  ·
                    refine ⟨930984243617537585161789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1241312324823383446882385 930984243617537585161789)
                    ·
                      refine ⟨349119091356576594435671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930984243617537585161789 349119091356576594435671)
                      ·
                        rfl

theorem cell23_679907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_679907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679907 prefixEnd_679907 := by exact prefixLift 679907
  have htrace : WordTrace (prefixWord ++ tailWord_679907) baseStart_679907 baseEnd_679907 := by
    simpa [prefixWord, tailWord_679907, baseEnd_679907] using wordTrace_append hprefix tailTrace_679907
  have hstable : (prefixWord ++ tailWord_679907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679907).length < 2 ^ (prefixWord ++ tailWord_679907).sum := by decide
  have hdescent : baseEnd_679907 < baseStart_679907 := by decide
  rcases family_descends (prefixWord ++ tailWord_679907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679920 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3]
def baseStart_679920 : Nat := 118140960795 + 679920 * 2 ^ 59
def prefixEnd_679920 : Nat := 4983230072969 + 3 ^ 40 * 679920 * 2
def baseEnd_679920 : Nat := 349125766605085043573111

theorem tailTrace_679920 : CollatzResearch.WordTrace tailWord_679920 prefixEnd_679920 349125766605085043573111 := by
  unfold tailWord_679920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12399359848386717968118607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16532479797848957290824809 12399359848386717968118607)
  ·
    refine ⟨18599039772580076952177911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12399359848386717968118607 18599039772580076952177911)
    ·
      refine ⟨27898559658870115428266867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18599039772580076952177911 27898559658870115428266867)
      ·
        refine ⟨41847839488305173142400301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27898559658870115428266867 41847839488305173142400301)
        ·
          refine ⟨15692939808114439928400113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41847839488305173142400301 15692939808114439928400113)
          ·
            refine ⟨11769704856085829946300085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15692939808114439928400113 11769704856085829946300085)
            ·
              refine ⟨1103409830258046557465633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11769704856085829946300085 1103409830258046557465633)
              ·
                refine ⟨827557372693534918099225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103409830258046557465633 827557372693534918099225)
                ·
                  refine ⟨620668029520151188574419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827557372693534918099225 620668029520151188574419)
                  ·
                    refine ⟨931002044280226782861629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620668029520151188574419 931002044280226782861629)
                    ·
                      refine ⟨349125766605085043573111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931002044280226782861629 349125766605085043573111)
                      ·
                        rfl

theorem cell23_679920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_679920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679920 prefixEnd_679920 := by exact prefixLift 679920
  have htrace : WordTrace (prefixWord ++ tailWord_679920) baseStart_679920 baseEnd_679920 := by
    simpa [prefixWord, tailWord_679920, baseEnd_679920] using wordTrace_append hprefix tailTrace_679920
  have hstable : (prefixWord ++ tailWord_679920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679920).length < 2 ^ (prefixWord ++ tailWord_679920).sum := by decide
  have hdescent : baseEnd_679920 < baseStart_679920 := by decide
  rcases family_descends (prefixWord ++ tailWord_679920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679937 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_679937 : Nat := 118140960795 + 679937 * 2 ^ 59
def prefixEnd_679937 : Nat := 4983230072969 + 3 ^ 40 * 679937 * 2
def baseEnd_679937 : Nat := 349134495776211477060533

theorem tailTrace_679937 : CollatzResearch.WordTrace tailWord_679937 prefixEnd_679937 349134495776211477060533 := by
  unfold tailWord_679937
  simp only [CollatzResearch.WordTrace]
  refine ⟨24799339737711847839606065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16532893158474565226404043 24799339737711847839606065)
  ·
    refine ⟨18599504803283885879704549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24799339737711847839606065 18599504803283885879704549)
    ·
      refine ⟨3487407150615728602444603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18599504803283885879704549 3487407150615728602444603)
      ·
        refine ⟨5231110725923592903666905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487407150615728602444603 5231110725923592903666905)
        ·
          refine ⟨3923333044442694677750179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231110725923592903666905 3923333044442694677750179)
          ·
            refine ⟨5884999566664042016625269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923333044442694677750179 5884999566664042016625269)
            ·
              refine ⟨551718709374753939058619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5884999566664042016625269 551718709374753939058619)
              ·
                refine ⟨827578064062130908587929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551718709374753939058619 827578064062130908587929)
                ·
                  refine ⟨620683548046598181440947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827578064062130908587929 620683548046598181440947)
                  ·
                    refine ⟨931025322069897272161421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620683548046598181440947 931025322069897272161421)
                    ·
                      refine ⟨349134495776211477060533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931025322069897272161421 349134495776211477060533)
                      ·
                        rfl

theorem cell23_679937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_679937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679937 prefixEnd_679937 := by exact prefixLift 679937
  have htrace : WordTrace (prefixWord ++ tailWord_679937) baseStart_679937 baseEnd_679937 := by
    simpa [prefixWord, tailWord_679937, baseEnd_679937] using wordTrace_append hprefix tailTrace_679937
  have hstable : (prefixWord ++ tailWord_679937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679937).length < 2 ^ (prefixWord ++ tailWord_679937).sum := by decide
  have hdescent : baseEnd_679937 < baseStart_679937 := by decide
  rcases family_descends (prefixWord ++ tailWord_679937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679960 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_679960 : Nat := 118140960795 + 679960 * 2 ^ 59
def prefixEnd_679960 : Nat := 4983230072969 + 3 ^ 40 * 679960 * 2
def baseEnd_679960 : Nat := 349146305831264887072927

theorem tailTrace_679960 : CollatzResearch.WordTrace tailWord_679960 prefixEnd_679960 349146305831264887072927 := by
  unfold tailWord_679960
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400089308314261383846667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16533452411085681845128889 12400089308314261383846667)
  ·
    refine ⟨18600133962471392075770001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12400089308314261383846667 18600133962471392075770001)
    ·
      refine ⟨13950100471853544056827501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18600133962471392075770001 13950100471853544056827501)
      ·
        refine ⟨5231287676945079021310313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13950100471853544056827501 5231287676945079021310313)
        ·
          refine ⟨3923465757708809265982735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231287676945079021310313 3923465757708809265982735)
          ·
            refine ⟨5885198636563213898974103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923465757708809265982735 5885198636563213898974103)
            ·
              refine ⟨8827797954844820848461155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885198636563213898974103 8827797954844820848461155)
              ·
                refine ⟨13241696932267231272691733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8827797954844820848461155 13241696932267231272691733)
                ·
                  refine ⟨620704543700026465907425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13241696932267231272691733 620704543700026465907425)
                  ·
                    refine ⟨465528407775019849430569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 620704543700026465907425 465528407775019849430569)
                    ·
                      refine ⟨349146305831264887072927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 465528407775019849430569 349146305831264887072927)
                      ·
                        rfl

theorem cell23_679960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_679960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679960 prefixEnd_679960 := by exact prefixLift 679960
  have htrace : WordTrace (prefixWord ++ tailWord_679960) baseStart_679960 baseEnd_679960 := by
    simpa [prefixWord, tailWord_679960, baseEnd_679960] using wordTrace_append hprefix tailTrace_679960
  have hstable : (prefixWord ++ tailWord_679960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679960).length < 2 ^ (prefixWord ++ tailWord_679960).sum := by decide
  have hdescent : baseEnd_679960 < baseStart_679960 := by decide
  rcases family_descends (prefixWord ++ tailWord_679960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679988 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_679988 : Nat := 118140960795 + 679988 * 2 ^ 59
def prefixEnd_679988 : Nat := 4983230072969 + 3 ^ 40 * 679988 * 2
def baseEnd_679988 : Nat := 349160683289590777522799

theorem tailTrace_679988 : CollatzResearch.WordTrace tailWord_679988 prefixEnd_679988 349160683289590777522799 := by
  unfold tailWord_679988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400599930263541774856309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16534133240351389033141745 12400599930263541774856309)
  ·
    refine ⟨1162556243462207041392779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12400599930263541774856309 1162556243462207041392779)
    ·
      refine ⟨1743834365193310562089169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162556243462207041392779 1743834365193310562089169)
      ·
        refine ⟨1307875773894982921566877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743834365193310562089169 1307875773894982921566877)
        ·
          refine ⟨490453415210618595587579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1307875773894982921566877 490453415210618595587579)
          ·
            refine ⟨735680122815927893381369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490453415210618595587579 735680122815927893381369)
            ·
              refine ⟨551760092111945920036027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735680122815927893381369 551760092111945920036027)
              ·
                refine ⟨827640138167918880054041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551760092111945920036027 827640138167918880054041)
                ·
                  refine ⟨620730103625939160040531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827640138167918880054041 620730103625939160040531)
                  ·
                    refine ⟨931095155438908740060797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620730103625939160040531 931095155438908740060797)
                    ·
                      refine ⟨349160683289590777522799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931095155438908740060797 349160683289590777522799)
                      ·
                        rfl

theorem cell23_679988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_679988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679988 prefixEnd_679988 := by exact prefixLift 679988
  have htrace : WordTrace (prefixWord ++ tailWord_679988) baseStart_679988 baseEnd_679988 := by
    simpa [prefixWord, tailWord_679988, baseEnd_679988] using wordTrace_append hprefix tailTrace_679988
  have hstable : (prefixWord ++ tailWord_679988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679988).length < 2 ^ (prefixWord ++ tailWord_679988).sum := by decide
  have hdescent : baseEnd_679988 < baseStart_679988 := by decide
  rcases family_descends (prefixWord ++ tailWord_679988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680003 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 4, 5, 2]
def baseStart_680003 : Nat := 118140960795 + 680003 * 2 ^ 59
def prefixEnd_680003 : Nat := 4983230072969 + 3 ^ 40 * 680003 * 2
def baseEnd_680003 : Nat := 349168385499408218835229

theorem tailTrace_680003 : CollatzResearch.WordTrace tailWord_680003 prefixEnd_680003 349168385499408218835229 := by
  unfold tailWord_680003
  simp only [CollatzResearch.WordTrace]
  refine ⟨24801746955472741111508663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16534497970315160741005775 24801746955472741111508663)
  ·
    refine ⟨37202620433209111667262995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24801746955472741111508663 37202620433209111667262995)
    ·
      refine ⟨55803930649813667500894493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37202620433209111667262995 55803930649813667500894493)
      ·
        refine ⟨20926473993680125312835435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55803930649813667500894493 20926473993680125312835435)
        ·
          refine ⟨31389710990520187969253153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20926473993680125312835435 31389710990520187969253153)
          ·
            refine ⟨23542283242890140976939865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31389710990520187969253153 23542283242890140976939865)
            ·
              refine ⟨17656712432167605732704899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23542283242890140976939865 17656712432167605732704899)
              ·
                refine ⟨26485068648251408599057349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17656712432167605732704899 26485068648251408599057349)
                ·
                  refine ⟨4965950371547139112323253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26485068648251408599057349 4965950371547139112323253)
                  ·
                    refine ⟨465557847332544291780305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4965950371547139112323253 465557847332544291780305)
                    ·
                      refine ⟨349168385499408218835229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 465557847332544291780305 349168385499408218835229)
                      ·
                        rfl

theorem cell23_680003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_680003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680003 prefixEnd_680003 := by exact prefixLift 680003
  have htrace : WordTrace (prefixWord ++ tailWord_680003) baseStart_680003 baseEnd_680003 := by
    simpa [prefixWord, tailWord_680003, baseEnd_680003] using wordTrace_append hprefix tailTrace_680003
  have hstable : (prefixWord ++ tailWord_680003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680003).length < 2 ^ (prefixWord ++ tailWord_680003).sum := by decide
  have hdescent : baseEnd_680003 < baseStart_680003 := by decide
  rcases family_descends (prefixWord ++ tailWord_680003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680050 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_680050 : Nat := 118140960795 + 680050 * 2 ^ 59
def prefixEnd_680050 : Nat := 4983230072969 + 3 ^ 40 * 680050 * 2
def baseEnd_680050 : Nat := 349192519090169534947513

theorem tailTrace_680050 : CollatzResearch.WordTrace tailWord_680050 prefixEnd_680050 349192519090169534947513 := by
  unfold tailWord_680050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200865296575617034617401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16535640790868312092313069 6200865296575617034617401)
  ·
    refine ⟨4650648972431712775963051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6200865296575617034617401 4650648972431712775963051)
    ·
      refine ⟨6975973458647569163944577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4650648972431712775963051 6975973458647569163944577)
      ·
        refine ⟨5231980093985676872958433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6975973458647569163944577 5231980093985676872958433)
        ·
          refine ⟨3923985070489257654718825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231980093985676872958433 3923985070489257654718825)
          ·
            refine ⟨2942988802866943241039119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3923985070489257654718825 2942988802866943241039119)
            ·
              refine ⟨4414483204300414861558679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942988802866943241039119 4414483204300414861558679)
              ·
                refine ⟨6621724806450622292338019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414483204300414861558679 6621724806450622292338019)
                ·
                  refine ⟨9932587209675933438507029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621724806450622292338019 9932587209675933438507029)
                  ·
                    refine ⟨465590025453559379930017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9932587209675933438507029 465590025453559379930017)
                    ·
                      refine ⟨349192519090169534947513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 465590025453559379930017 349192519090169534947513)
                      ·
                        rfl

theorem cell23_680050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_680050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680050 prefixEnd_680050 := by exact prefixLift 680050
  have htrace : WordTrace (prefixWord ++ tailWord_680050) baseStart_680050 baseEnd_680050 := by
    simpa [prefixWord, tailWord_680050, baseEnd_680050] using wordTrace_append hprefix tailTrace_680050
  have hstable : (prefixWord ++ tailWord_680050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680050).length < 2 ^ (prefixWord ++ tailWord_680050).sum := by decide
  have hdescent : baseEnd_680050 < baseStart_680050 := by decide
  rcases family_descends (prefixWord ++ tailWord_680050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680056 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 10]
def baseStart_680056 : Nat := 118140960795 + 680056 * 2 ^ 59
def prefixEnd_680056 : Nat := 4983230072969 + 3 ^ 40 * 680056 * 2
def baseEnd_680056 : Nat := 38799511108232945719165

theorem tailTrace_680056 : CollatzResearch.WordTrace tailWord_680056 prefixEnd_680056 38799511108232945719165 := by
  unfold tailWord_680056
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401840012140365581594011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16535786682853820775458681 12401840012140365581594011)
  ·
    refine ⟨18602760018210548372391017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12401840012140365581594011 18602760018210548372391017)
    ·
      refine ⟨13952070013657911279293263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18602760018210548372391017 13952070013657911279293263)
      ·
        refine ⟨20928105020486866918939895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13952070013657911279293263 20928105020486866918939895)
        ·
          refine ⟨31392157530730300378409843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20928105020486866918939895 31392157530730300378409843)
          ·
            refine ⟨47088236296095450567614765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31392157530730300378409843 47088236296095450567614765)
            ·
              refine ⟨17658088611035793962855537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47088236296095450567614765 17658088611035793962855537)
              ·
                refine ⟨13243566458276845472141653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17658088611035793962855537 13243566458276845472141653)
                ·
                  refine ⟨38799511108232945719165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13243566458276845472141653 38799511108232945719165)
                  ·
                    rfl

theorem cell23_680056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_680056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680056 prefixEnd_680056 := by exact prefixLift 680056
  have htrace : WordTrace (prefixWord ++ tailWord_680056) baseStart_680056 baseEnd_680056 := by
    simpa [prefixWord, tailWord_680056, baseEnd_680056] using wordTrace_append hprefix tailTrace_680056
  have hstable : (prefixWord ++ tailWord_680056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680056).length < 2 ^ (prefixWord ++ tailWord_680056).sum := by decide
  have hdescent : baseEnd_680056 < baseStart_680056 := by decide
  rcases family_descends (prefixWord ++ tailWord_680056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680060 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_680060 : Nat := 118140960795 + 680060 * 2 ^ 59
def prefixEnd_680060 : Nat := 4983230072969 + 3 ^ 40 * 680060 * 2
def baseEnd_680060 : Nat := 116399217965571498607489

theorem tailTrace_680060 : CollatzResearch.WordTrace tailWord_680060 prefixEnd_680060 116399217965571498607489 := by
  unfold tailWord_680060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401912958133119923166817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16535883944177493230889089 12401912958133119923166817)
  ·
    refine ⟨9301434718599839942375113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12401912958133119923166817 9301434718599839942375113)
    ·
      refine ⟨6976076038949879956781335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9301434718599839942375113 6976076038949879956781335)
      ·
        refine ⟨10464114058424819935172003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976076038949879956781335 10464114058424819935172003)
        ·
          refine ⟨15696171087637229902758005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10464114058424819935172003 15696171087637229902758005)
          ·
            refine ⟨1471516039465990303383563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15696171087637229902758005 1471516039465990303383563)
            ·
              refine ⟨2207274059198985455075345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471516039465990303383563 2207274059198985455075345)
              ·
                refine ⟨1655455544399239091306509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207274059198985455075345 1655455544399239091306509)
                ·
                  refine ⟨620795829149714659239941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1655455544399239091306509 620795829149714659239941)
                  ·
                    refine ⟨116399217965571498607489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620795829149714659239941 116399217965571498607489)
                    ·
                      rfl

theorem cell23_680060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_680060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680060 prefixEnd_680060 := by exact prefixLift 680060
  have htrace : WordTrace (prefixWord ++ tailWord_680060) baseStart_680060 baseEnd_680060 := by
    simpa [prefixWord, tailWord_680060, baseEnd_680060] using wordTrace_append hprefix tailTrace_680060
  have hstable : (prefixWord ++ tailWord_680060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680060).length < 2 ^ (prefixWord ++ tailWord_680060).sum := by decide
  have hdescent : baseEnd_680060 < baseStart_680060 := by decide
  rcases family_descends (prefixWord ++ tailWord_680060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680090 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_680090 : Nat := 118140960795 + 680090 * 2 ^ 59
def prefixEnd_680090 : Nat := 4983230072969 + 3 ^ 40 * 680090 * 2
def baseEnd_680090 : Nat := 38801450924038819827481

theorem tailTrace_680090 : CollatzResearch.WordTrace tailWord_680090 prefixEnd_680090 38801450924038819827481 := by
  unfold tailWord_680090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201230026539388742481431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16536613404105036646617149 6201230026539388742481431)
  ·
    refine ⟨9301845039809083113722147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201230026539388742481431 9301845039809083113722147)
    ·
      refine ⟨13952767559713624670583221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301845039809083113722147 13952767559713624670583221)
      ·
        refine ⟨1308071958723152312867177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13952767559713624670583221 1308071958723152312867177)
        ·
          refine ⟨981053969042364234650383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308071958723152312867177 981053969042364234650383)
          ·
            refine ⟨1471580953563546351975575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981053969042364234650383 1471580953563546351975575)
            ·
              refine ⟨2207371430345319527963363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471580953563546351975575 2207371430345319527963363)
              ·
                refine ⟨3311057145517979291945045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207371430345319527963363 3311057145517979291945045)
                ·
                  refine ⟨38801450924038819827481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3311057145517979291945045 38801450924038819827481)
                  ·
                    rfl

theorem cell23_680090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_680090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680090 prefixEnd_680090 := by exact prefixLift 680090
  have htrace : WordTrace (prefixWord ++ tailWord_680090) baseStart_680090 baseEnd_680090 := by
    simpa [prefixWord, tailWord_680090, baseEnd_680090] using wordTrace_append hprefix tailTrace_680090
  have hstable : (prefixWord ++ tailWord_680090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680090).length < 2 ^ (prefixWord ++ tailWord_680090).sum := by decide
  have hdescent : baseEnd_680090 < baseStart_680090 := by decide
  rcases family_descends (prefixWord ++ tailWord_680090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680093 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_680093 : Nat := 118140960795 + 680093 * 2 ^ 59
def prefixEnd_680093 : Nat := 4983230072969 + 3 ^ 40 * 680093 * 2
def baseEnd_680093 : Nat := 349214598758312866709815

theorem tailTrace_680093 : CollatzResearch.WordTrace tailWord_680093 prefixEnd_680093 349214598758312866709815 := by
  unfold tailWord_680093
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805029525146686482284933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16536686350097790988189955 24805029525146686482284933)
  ·
    refine ⟨4650943035965003715428425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24805029525146686482284933 4650943035965003715428425)
    ·
      refine ⟨3488207276973752786571319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4650943035965003715428425 3488207276973752786571319)
      ·
        refine ⟨5232310915460629179856979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488207276973752786571319 5232310915460629179856979)
        ·
          refine ⟨7848466373190943769785469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232310915460629179856979 7848466373190943769785469)
          ·
            refine ⟨2943174889946603913669551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7848466373190943769785469 2943174889946603913669551)
            ·
              refine ⟨4414762334919905870504327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943174889946603913669551 4414762334919905870504327)
              ·
                refine ⟨6622143502379858805756491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414762334919905870504327 6622143502379858805756491)
                ·
                  refine ⟨9933215253569788208634737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622143502379858805756491 9933215253569788208634737)
                  ·
                    refine ⟨7449911440177341156476053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9933215253569788208634737 7449911440177341156476053)
                    ·
                      refine ⟨349214598758312866709815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7449911440177341156476053 349214598758312866709815)
                      ·
                        rfl

theorem cell23_680093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_680093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680093 prefixEnd_680093 := by exact prefixLift 680093
  have htrace : WordTrace (prefixWord ++ tailWord_680093) baseStart_680093 baseEnd_680093 := by
    simpa [prefixWord, tailWord_680093, baseEnd_680093] using wordTrace_append hprefix tailTrace_680093
  have hstable : (prefixWord ++ tailWord_680093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680093).length < 2 ^ (prefixWord ++ tailWord_680093).sum := by decide
  have hdescent : baseEnd_680093 < baseStart_680093 := by decide
  rcases family_descends (prefixWord ++ tailWord_680093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680094 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_680094 : Nat := 118140960795 + 680094 * 2 ^ 59
def prefixEnd_680094 : Nat := 4983230072969 + 3 ^ 40 * 680094 * 2
def baseEnd_680094 : Nat := 116405037412989120932437

theorem tailTrace_680094 : CollatzResearch.WordTrace tailWord_680094 prefixEnd_680094 116405037412989120932437 := by
  unfold tailWord_680094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100633249767882956633917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16536710665428709102047557 3100633249767882956633917)
  ·
    refine ⟨1162737468662956108737719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3100633249767882956633917 1162737468662956108737719)
    ·
      refine ⟨1744106202994434163106579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162737468662956108737719 1744106202994434163106579)
      ·
        refine ⟨2616159304491651244659869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744106202994434163106579 2616159304491651244659869)
        ·
          refine ⟨981059739184369216747451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2616159304491651244659869 981059739184369216747451)
          ·
            refine ⟨1471589608776553825121177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981059739184369216747451 1471589608776553825121177)
            ·
              refine ⟨1103692206582415368840883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471589608776553825121177 1103692206582415368840883)
              ·
                refine ⟨1655538309873623053261325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103692206582415368840883 1655538309873623053261325)
                ·
                  refine ⟨620826866202608644972997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1655538309873623053261325 620826866202608644972997)
                  ·
                    refine ⟨116405037412989120932437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620826866202608644972997 116405037412989120932437)
                    ·
                      rfl

theorem cell23_680094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_680094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680094 prefixEnd_680094 := by exact prefixLift 680094
  have htrace : WordTrace (prefixWord ++ tailWord_680094) baseStart_680094 baseEnd_680094 := by
    simpa [prefixWord, tailWord_680094, baseEnd_680094] using wordTrace_append hprefix tailTrace_680094
  have hstable : (prefixWord ++ tailWord_680094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680094).length < 2 ^ (prefixWord ++ tailWord_680094).sum := by decide
  have hdescent : baseEnd_680094 < baseStart_680094 := by decide
  rcases family_descends (prefixWord ++ tailWord_680094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680120 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_680120 : Nat := 118140960795 + 680120 * 2 ^ 59
def prefixEnd_680120 : Nat := 4983230072969 + 3 ^ 40 * 680120 * 2
def baseEnd_680120 : Nat := 116409487578661420357397

theorem tailTrace_680120 : CollatzResearch.WordTrace tailWord_680120 prefixEnd_680120 116409487578661420357397 := by
  unfold tailWord_680120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403007148024435046758907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16537342864032580062345209 12403007148024435046758907)
  ·
    refine ⟨18604510722036652570138361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12403007148024435046758907 18604510722036652570138361)
    ·
      refine ⟨13953383041527489427603771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18604510722036652570138361 13953383041527489427603771)
      ·
        refine ⟨20930074562291234141405657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953383041527489427603771 20930074562291234141405657)
        ·
          refine ⟨15697555921718425606054243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20930074562291234141405657 15697555921718425606054243)
          ·
            refine ⟨23546333882577638409081365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15697555921718425606054243 23546333882577638409081365)
            ·
              refine ⟨1103734400745826800425689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23546333882577638409081365 1103734400745826800425689)
              ·
                refine ⟨827800800559370100319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103734400745826800425689 827800800559370100319267)
                ·
                  refine ⟨1241701200839055150478901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827800800559370100319267 1241701200839055150478901)
                  ·
                    refine ⟨116409487578661420357397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1241701200839055150478901 116409487578661420357397)
                    ·
                      rfl

theorem cell23_680120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_680120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680120 prefixEnd_680120 := by exact prefixLift 680120
  have htrace : WordTrace (prefixWord ++ tailWord_680120) baseStart_680120 baseEnd_680120 := by
    simpa [prefixWord, tailWord_680120, baseEnd_680120] using wordTrace_append hprefix tailTrace_680120
  have hstable : (prefixWord ++ tailWord_680120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680120).length < 2 ^ (prefixWord ++ tailWord_680120).sum := by decide
  have hdescent : baseEnd_680120 < baseStart_680120 := by decide
  rcases family_descends (prefixWord ++ tailWord_680120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680133 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_680133 : Nat := 118140960795 + 680133 * 2 ^ 59
def prefixEnd_680133 : Nat := 4983230072969 + 3 ^ 40 * 680133 * 2
def baseEnd_680133 : Nat := 116411712661497570069877

theorem tailTrace_680133 : CollatzResearch.WordTrace tailWord_680133 prefixEnd_680133 116411712661497570069877 := by
  unfold tailWord_680133
  simp only [CollatzResearch.WordTrace]
  refine ⟨24806488445001773313741053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16537658963334515542494035 24806488445001773313741053)
  ·
    refine ⟨9302433166875664992652895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24806488445001773313741053 9302433166875664992652895)
    ·
      refine ⟨13953649750313497488979343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302433166875664992652895 13953649750313497488979343)
      ·
        refine ⟨20930474625470246233469015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953649750313497488979343 20930474625470246233469015)
        ·
          refine ⟨31395711938205369350203523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20930474625470246233469015 31395711938205369350203523)
          ·
            refine ⟨47093567907308054025305285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31395711938205369350203523 47093567907308054025305285)
            ·
              refine ⟨8830043982620260129744741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47093567907308054025305285 8830043982620260129744741)
              ·
                refine ⟨1655633246741298774327139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8830043982620260129744741 1655633246741298774327139)
                ·
                  refine ⟨2483449870111948161490709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655633246741298774327139 2483449870111948161490709)
                  ·
                    refine ⟨116411712661497570069877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2483449870111948161490709 116411712661497570069877)
                    ·
                      rfl

theorem cell23_680133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_680133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680133 prefixEnd_680133 := by exact prefixLift 680133
  have htrace : WordTrace (prefixWord ++ tailWord_680133) baseStart_680133 baseEnd_680133 := by
    simpa [prefixWord, tailWord_680133, baseEnd_680133] using wordTrace_append hprefix tailTrace_680133
  have hstable : (prefixWord ++ tailWord_680133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680133).length < 2 ^ (prefixWord ++ tailWord_680133).sum := by decide
  have hdescent : baseEnd_680133 < baseStart_680133 := by decide
  rcases family_descends (prefixWord ++ tailWord_680133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680153 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_680153 : Nat := 118140960795 + 680153 * 2 ^ 59
def prefixEnd_680153 : Nat := 4983230072969 + 3 ^ 40 * 680153 * 2
def baseEnd_680153 : Nat := 349245407597582631959539

theorem tailTrace_680153 : CollatzResearch.WordTrace tailWord_680153 prefixEnd_680153 349245407597582631959539 := by
  unfold tailWord_680153
  simp only [CollatzResearch.WordTrace]
  refine ⟨24807217904929316729469113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16538145269952877819646075 24807217904929316729469113)
  ·
    refine ⟨18605413428696987547101835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24807217904929316729469113 18605413428696987547101835)
    ·
      refine ⟨27908120143045481320652753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18605413428696987547101835 27908120143045481320652753)
      ·
        refine ⟨20931090107284110990489565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27908120143045481320652753 20931090107284110990489565)
        ·
          refine ⟨7849158790231541621433587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20931090107284110990489565 7849158790231541621433587)
          ·
            refine ⟨11773738185347312432150381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849158790231541621433587 11773738185347312432150381)
            ·
              refine ⟨4415151819505242162056393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11773738185347312432150381 4415151819505242162056393)
              ·
                refine ⟨3311363864628931621542295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4415151819505242162056393 3311363864628931621542295)
                ·
                  refine ⟨4967045796943397432313443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311363864628931621542295 4967045796943397432313443)
                  ·
                    refine ⟨7450568695415096148470165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4967045796943397432313443 7450568695415096148470165)
                    ·
                      refine ⟨349245407597582631959539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7450568695415096148470165 349245407597582631959539)
                      ·
                        rfl

theorem cell23_680153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_680153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680153 prefixEnd_680153 := by exact prefixLift 680153
  have htrace : WordTrace (prefixWord ++ tailWord_680153) baseStart_680153 baseEnd_680153 := by
    simpa [prefixWord, tailWord_680153, baseEnd_680153] using wordTrace_append hprefix tailTrace_680153
  have hstable : (prefixWord ++ tailWord_680153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680153).length < 2 ^ (prefixWord ++ tailWord_680153).sum := by decide
  have hdescent : baseEnd_680153 < baseStart_680153 := by decide
  rcases family_descends (prefixWord ++ tailWord_680153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680160 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_680160 : Nat := 118140960795 + 680160 * 2 ^ 59
def prefixEnd_680160 : Nat := 4983230072969 + 3 ^ 40 * 680160 * 2
def baseEnd_680160 : Nat := 349249001962164104572007

theorem tailTrace_680160 : CollatzResearch.WordTrace tailWord_680160 prefixEnd_680160 349249001962164104572007 := by
  unfold tailWord_680160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403736607951978462486967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16538315477269304616649289 12403736607951978462486967)
  ·
    refine ⟨18605604911927967693730451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12403736607951978462486967 18605604911927967693730451)
    ·
      refine ⟨27908407367891951540595677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18605604911927967693730451 27908407367891951540595677)
      ·
        refine ⟨10465652762959481827723379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27908407367891951540595677 10465652762959481827723379)
        ·
          refine ⟨15698479144439222741585069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465652762959481827723379 15698479144439222741585069)
          ·
            refine ⟨5886929679164708528094401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15698479144439222741585069 5886929679164708528094401)
            ·
              refine ⟨4415197259373531396070801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5886929679164708528094401 4415197259373531396070801)
              ·
                refine ⟨3311397944530148547053101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4415197259373531396070801 3311397944530148547053101)
                ·
                  refine ⟨1241774229198805705144913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3311397944530148547053101 1241774229198805705144913)
                  ·
                    refine ⟨931330671899104278858685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1241774229198805705144913 931330671899104278858685)
                    ·
                      refine ⟨349249001962164104572007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931330671899104278858685 349249001962164104572007)
                      ·
                        rfl

theorem cell23_680160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_680160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680160 prefixEnd_680160 := by exact prefixLift 680160
  have htrace : WordTrace (prefixWord ++ tailWord_680160) baseStart_680160 baseEnd_680160 := by
    simpa [prefixWord, tailWord_680160, baseEnd_680160] using wordTrace_append hprefix tailTrace_680160
  have hstable : (prefixWord ++ tailWord_680160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680160).length < 2 ^ (prefixWord ++ tailWord_680160).sum := by decide
  have hdescent : baseEnd_680160 < baseStart_680160 := by decide
  rcases family_descends (prefixWord ++ tailWord_680160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680170 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_680170 : Nat := 118140960795 + 680170 * 2 ^ 59
def prefixEnd_680170 : Nat := 4983230072969 + 3 ^ 40 * 680170 * 2
def baseEnd_680170 : Nat := 349254136768709065446961

theorem tailTrace_680170 : CollatzResearch.WordTrace tailWord_680170 prefixEnd_680170 349254136768709065446961 := by
  unfold tailWord_680170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201959486466932158209491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16538558630578485755225309 6201959486466932158209491)
  ·
    refine ⟨9302939229700398237314237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201959486466932158209491 9302939229700398237314237)
    ·
      refine ⟨3488602211137649338992839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9302939229700398237314237 3488602211137649338992839)
      ·
        refine ⟨5232903316706474008489259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488602211137649338992839 5232903316706474008489259)
        ·
          refine ⟨7849354975059711012733889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232903316706474008489259 7849354975059711012733889)
          ·
            refine ⟨5887016231294783259550417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7849354975059711012733889 5887016231294783259550417)
            ·
              refine ⟨4415262173471087444662813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887016231294783259550417 4415262173471087444662813)
              ·
                refine ⟨1655723315051657791748555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4415262173471087444662813 1655723315051657791748555)
                ·
                  refine ⟨2483584972577486687622833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655723315051657791748555 2483584972577486687622833)
                  ·
                    refine ⟨1862688729433115015717125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2483584972577486687622833 1862688729433115015717125)
                    ·
                      refine ⟨349254136768709065446961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1862688729433115015717125 349254136768709065446961)
                      ·
                        rfl

theorem cell23_680170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_680170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680170 prefixEnd_680170 := by exact prefixLift 680170
  have htrace : WordTrace (prefixWord ++ tailWord_680170) baseStart_680170 baseEnd_680170 := by
    simpa [prefixWord, tailWord_680170, baseEnd_680170] using wordTrace_append hprefix tailTrace_680170
  have hstable : (prefixWord ++ tailWord_680170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680170).length < 2 ^ (prefixWord ++ tailWord_680170).sum := by decide
  have hdescent : baseEnd_680170 < baseStart_680170 := by decide
  rcases family_descends (prefixWord ++ tailWord_680170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680177 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_680177 : Nat := 118140960795 + 680177 * 2 ^ 59
def prefixEnd_680177 : Nat := 4983230072969 + 3 ^ 40 * 680177 * 2
def baseEnd_680177 : Nat := 349257731133290538059429

theorem tailTrace_680177 : CollatzResearch.WordTrace tailWord_680177 prefixEnd_680177 349257731133290538059429 := by
  unfold tailWord_680177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808093256842368828342785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16538728837894912552228523 24808093256842368828342785)
  ·
    refine ⟨18606069942631776621257089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24808093256842368828342785 18606069942631776621257089)
    ·
      refine ⟨13954552456973832465942817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18606069942631776621257089 13954552456973832465942817)
      ·
        refine ⟨10465914342730374349457113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13954552456973832465942817 10465914342730374349457113)
        ·
          refine ⟨7849435757047780762092835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10465914342730374349457113 7849435757047780762092835)
          ·
            refine ⟨11774153635571671143139253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849435757047780762092835 11774153635571671143139253)
            ·
              refine ⟨1103826903334844169669305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11774153635571671143139253 1103826903334844169669305)
              ·
                refine ⟨827870177501133127251979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103826903334844169669305 827870177501133127251979)
                ·
                  refine ⟨1241805266251699690877969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827870177501133127251979 1241805266251699690877969)
                  ·
                    refine ⟨931353949688774768158477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1241805266251699690877969 931353949688774768158477)
                    ·
                      refine ⟨349257731133290538059429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931353949688774768158477 349257731133290538059429)
                      ·
                        rfl

theorem cell23_680177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_680177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680177 prefixEnd_680177 := by exact prefixLift 680177
  have htrace : WordTrace (prefixWord ++ tailWord_680177) baseStart_680177 baseEnd_680177 := by
    simpa [prefixWord, tailWord_680177, baseEnd_680177] using wordTrace_append hprefix tailTrace_680177
  have hstable : (prefixWord ++ tailWord_680177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680177).length < 2 ^ (prefixWord ++ tailWord_680177).sum := by decide
  have hdescent : baseEnd_680177 < baseStart_680177 := by decide
  rcases family_descends (prefixWord ++ tailWord_680177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680194 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_680194 : Nat := 118140960795 + 680194 * 2 ^ 59
def prefixEnd_680194 : Nat := 4983230072969 + 3 ^ 40 * 680194 * 2
def baseEnd_680194 : Nat := 349266460304416971546851

theorem tailTrace_680194 : CollatzResearch.WordTrace tailWord_680194 prefixEnd_680194 349266460304416971546851 := by
  unfold tailWord_680194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6202178324445195182927909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16539142198520520487807757 6202178324445195182927909)
  ·
    refine ⟨1162908435833474096798983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6202178324445195182927909 1162908435833474096798983)
    ·
      refine ⟨1744362653750211145198475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162908435833474096798983 1744362653750211145198475)
      ·
        refine ⟨2616543980625316717797713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744362653750211145198475 2616543980625316717797713)
        ·
          refine ⟨1962407985468987538348285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2616543980625316717797713 1962407985468987538348285)
          ·
            refine ⟨735902994550870326880607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1962407985468987538348285 735902994550870326880607)
            ·
              refine ⟨1103854491826305490320911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735902994550870326880607 1103854491826305490320911)
              ·
                refine ⟨1655781737739458235481367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103854491826305490320911 1655781737739458235481367)
                ·
                  refine ⟨2483672606609187353222051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655781737739458235481367 2483672606609187353222051)
                  ·
                    refine ⟨3725508909913781029833077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2483672606609187353222051 3725508909913781029833077)
                    ·
                      refine ⟨349266460304416971546851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3725508909913781029833077 349266460304416971546851)
                      ·
                        rfl

theorem cell23_680194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_680194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680194 prefixEnd_680194 := by exact prefixLift 680194
  have htrace : WordTrace (prefixWord ++ tailWord_680194) baseStart_680194 baseEnd_680194 := by
    simpa [prefixWord, tailWord_680194, baseEnd_680194] using wordTrace_append hprefix tailTrace_680194
  have hstable : (prefixWord ++ tailWord_680194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680194).length < 2 ^ (prefixWord ++ tailWord_680194).sum := by decide
  have hdescent : baseEnd_680194 < baseStart_680194 := by decide
  rcases family_descends (prefixWord ++ tailWord_680194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680224 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3]
def baseStart_680224 : Nat := 118140960795 + 680224 * 2 ^ 59
def prefixEnd_680224 : Nat := 4983230072969 + 3 ^ 40 * 680224 * 2
def baseEnd_680224 : Nat := 349281864724051854171713

theorem tailTrace_680224 : CollatzResearch.WordTrace tailWord_680224 prefixEnd_680224 349281864724051854171713 := by
  unfold tailWord_680224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12404903743836047927651863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16539871658448063903535817 12404903743836047927651863)
  ·
    refine ⟨18607355615754071891477795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12404903743836047927651863 18607355615754071891477795)
    ·
      refine ⟨27911033423631107837216693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18607355615754071891477795 27911033423631107837216693)
      ·
        refine ⟨2616659383465416359739065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27911033423631107837216693 2616659383465416359739065)
        ·
          refine ⟨1962494537599062269804299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2616659383465416359739065 1962494537599062269804299)
          ·
            refine ⟨2943741806398593404706449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962494537599062269804299 2943741806398593404706449)
            ·
              refine ⟨2207806354798945053529837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943741806398593404706449 2207806354798945053529837)
              ·
                refine ⟨827927383049604395073689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2207806354798945053529837 827927383049604395073689)
                ·
                  refine ⟨620945537287203296305267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827927383049604395073689 620945537287203296305267)
                  ·
                    refine ⟨931418305930804944457901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620945537287203296305267 931418305930804944457901)
                    ·
                      refine ⟨349281864724051854171713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931418305930804944457901 349281864724051854171713)
                      ·
                        rfl

theorem cell23_680224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_680224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680224 prefixEnd_680224 := by exact prefixLift 680224
  have htrace : WordTrace (prefixWord ++ tailWord_680224) baseStart_680224 baseEnd_680224 := by
    simpa [prefixWord, tailWord_680224, baseEnd_680224] using wordTrace_append hprefix tailTrace_680224
  have hstable : (prefixWord ++ tailWord_680224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680224).length < 2 ^ (prefixWord ++ tailWord_680224).sum := by decide
  have hdescent : baseEnd_680224 < baseStart_680224 := by decide
  rcases family_descends (prefixWord ++ tailWord_680224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680231 : List Nat := [1, 1, 8, 1, 1, 1, 3, 7]
def baseStart_680231 : Nat := 118140960795 + 680231 * 2 ^ 59
def prefixEnd_680231 : Nat := 4983230072969 + 3 ^ 40 * 680231 * 2
def baseEnd_680231 : Nat := 12936498484764197288303

theorem tailTrace_680231 : CollatzResearch.WordTrace tailWord_680231 prefixEnd_680231 12936498484764197288303 := by
  unfold tailWord_680231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24810062798646736050808547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16540041865764490700539031 24810062798646736050808547)
  ·
    refine ⟨37215094197970104076212821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24810062798646736050808547 37215094197970104076212821)
    ·
      refine ⟨436114385132462157143119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 37215094197970104076212821 436114385132462157143119)
      ·
        refine ⟨654171577698693235714679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436114385132462157143119 654171577698693235714679)
        ·
          refine ⟨981257366548039853572019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654171577698693235714679 981257366548039853572019)
          ·
            refine ⟨1471886049822059780358029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981257366548039853572019 1471886049822059780358029)
            ·
              refine ⟨551957268683272417634261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1471886049822059780358029 551957268683272417634261)
              ·
                refine ⟨12936498484764197288303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 551957268683272417634261 12936498484764197288303)
                ·
                  rfl

theorem cell23_680231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 7].length) (baseStart_680231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680231 prefixEnd_680231 := by exact prefixLift 680231
  have htrace : WordTrace (prefixWord ++ tailWord_680231) baseStart_680231 baseEnd_680231 := by
    simpa [prefixWord, tailWord_680231, baseEnd_680231] using wordTrace_append hprefix tailTrace_680231
  have hstable : (prefixWord ++ tailWord_680231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680231).length < 2 ^ (prefixWord ++ tailWord_680231).sum := by decide
  have hdescent : baseEnd_680231 < baseStart_680231 := by decide
  rcases family_descends (prefixWord ++ tailWord_680231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680280 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_680280 : Nat := 118140960795 + 680280 * 2 ^ 59
def prefixEnd_680280 : Nat := 4983230072969 + 3 ^ 40 * 680280 * 2
def baseEnd_680280 : Nat := 349310619640703635071455

theorem tailTrace_680280 : CollatzResearch.WordTrace tailWord_680280 prefixEnd_680280 349310619640703635071455 := by
  unfold tailWord_680280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405924987734608709671147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16541233316979478279561529 12405924987734608709671147)
  ·
    refine ⟨18608887481601913064506721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12405924987734608709671147 18608887481601913064506721)
    ·
      refine ⟨13956665611201434798380041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18608887481601913064506721 13956665611201434798380041)
      ·
        refine ⟨10467499208401076098785031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13956665611201434798380041 10467499208401076098785031)
        ·
          refine ⟨15701248812601614148177547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467499208401076098785031 15701248812601614148177547)
          ·
            refine ⟨23551873218902421222266321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15701248812601614148177547 23551873218902421222266321)
            ·
              refine ⟨17663904914176815916699741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23551873218902421222266321 17663904914176815916699741)
              ·
                refine ⟨6623964342816305968762403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17663904914176815916699741 6623964342816305968762403)
                ·
                  refine ⟨9935946514224458953143605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6623964342816305968762403 9935946514224458953143605)
                  ·
                    refine ⟨931494985708543026857213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9935946514224458953143605 931494985708543026857213)
                    ·
                      refine ⟨349310619640703635071455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931494985708543026857213 349310619640703635071455)
                      ·
                        rfl

theorem cell23_680280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_680280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680280 prefixEnd_680280 := by exact prefixLift 680280
  have htrace : WordTrace (prefixWord ++ tailWord_680280) baseStart_680280 baseEnd_680280 := by
    simpa [prefixWord, tailWord_680280, baseEnd_680280] using wordTrace_append hprefix tailTrace_680280
  have hstable : (prefixWord ++ tailWord_680280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680280).length < 2 ^ (prefixWord ++ tailWord_680280).sum := by decide
  have hdescent : baseEnd_680280 < baseStart_680280 := by decide
  rcases family_descends (prefixWord ++ tailWord_680280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680304 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 5]
def baseStart_680304 : Nat := 118140960795 + 680304 * 2 ^ 59
def prefixEnd_680304 : Nat := 4983230072969 + 3 ^ 40 * 680304 * 2
def baseEnd_680304 : Nat := 38813660352934615685705

theorem tailTrace_680304 : CollatzResearch.WordTrace tailWord_680304 prefixEnd_680304 38813660352934615685705 := by
  unfold tailWord_680304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12406362663691134759107983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16541816884921513012143977 12406362663691134759107983)
  ·
    refine ⟨18609543995536702138661975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12406362663691134759107983 18609543995536702138661975)
    ·
      refine ⟨27914315993305053207992963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18609543995536702138661975 27914315993305053207992963)
      ·
        refine ⟨41871473989957579811989445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27914315993305053207992963 41871473989957579811989445)
        ·
          refine ⟨7850901373117046214748021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41871473989957579811989445 7850901373117046214748021)
          ·
            refine ⟨736022003729723082632627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7850901373117046214748021 736022003729723082632627)
            ·
              refine ⟨1104033005594584623948941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736022003729723082632627 1104033005594584623948941)
              ·
                refine ⟨414012377097969233980853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1104033005594584623948941 414012377097969233980853)
                ·
                  refine ⟨38813660352934615685705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414012377097969233980853 38813660352934615685705)
                  ·
                    rfl

theorem cell23_680304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 5].length) (baseStart_680304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680304 prefixEnd_680304 := by exact prefixLift 680304
  have htrace : WordTrace (prefixWord ++ tailWord_680304) baseStart_680304 baseEnd_680304 := by
    simpa [prefixWord, tailWord_680304, baseEnd_680304] using wordTrace_append hprefix tailTrace_680304
  have hstable : (prefixWord ++ tailWord_680304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680304).length < 2 ^ (prefixWord ++ tailWord_680304).sum := by decide
  have hdescent : baseEnd_680304 < baseStart_680304 := by decide
  rcases family_descends (prefixWord ++ tailWord_680304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680317 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_680317 : Nat := 118140960795 + 680317 * 2 ^ 59
def prefixEnd_680317 : Nat := 4983230072969 + 3 ^ 40 * 680317 * 2
def baseEnd_680317 : Nat := 116443206141639996769595

theorem tailTrace_680317 : CollatzResearch.WordTrace tailWord_680317 prefixEnd_680317 116443206141639996769595 := by
  unfold tailWord_680317
  simp only [CollatzResearch.WordTrace]
  refine ⟨24813199476335172738439205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16542132984223448492292803 24813199476335172738439205)
  ·
    refine ⟨4652474901812844888457351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24813199476335172738439205 4652474901812844888457351)
    ·
      refine ⟨6978712352719267332686027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652474901812844888457351 6978712352719267332686027)
      ·
        refine ⟨10468068529078900999029041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6978712352719267332686027 10468068529078900999029041)
        ·
          refine ⟨7851051396809175749271781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10468068529078900999029041 7851051396809175749271781)
          ·
            refine ⟨1472072136901720452988459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7851051396809175749271781 1472072136901720452988459)
            ·
              refine ⟨2208108205352580679482689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472072136901720452988459 2208108205352580679482689)
              ·
                refine ⟨1656081154014435509612017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208108205352580679482689 1656081154014435509612017)
                ·
                  refine ⟨1242060865510826632209013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1656081154014435509612017 1242060865510826632209013)
                  ·
                    refine ⟨116443206141639996769595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1242060865510826632209013 116443206141639996769595)
                    ·
                      rfl

theorem cell23_680317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_680317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680317 prefixEnd_680317 := by exact prefixLift 680317
  have htrace : WordTrace (prefixWord ++ tailWord_680317) baseStart_680317 baseEnd_680317 := by
    simpa [prefixWord, tailWord_680317, baseEnd_680317] using wordTrace_append hprefix tailTrace_680317
  have hstable : (prefixWord ++ tailWord_680317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680317).length < 2 ^ (prefixWord ++ tailWord_680317).sum := by decide
  have hdescent : baseEnd_680317 < baseStart_680317 := by decide
  rcases family_descends (prefixWord ++ tailWord_680317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680321 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 5]
def baseStart_680321 : Nat := 118140960795 + 680321 * 2 ^ 59
def prefixEnd_680321 : Nat := 4983230072969 + 3 ^ 40 * 680321 * 2
def baseEnd_680321 : Nat := 38814630260837552739863

theorem tailTrace_680321 : CollatzResearch.WordTrace tailWord_680321 prefixEnd_680321 38814630260837552739863 := by
  unfold tailWord_680321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24813345368320681421584817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16542230245547120947723211 24813345368320681421584817)
  ·
    refine ⟨18610009026240511066188613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24813345368320681421584817 18610009026240511066188613)
    ·
      refine ⟨3489376692420095824910365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18610009026240511066188613 3489376692420095824910365)
      ·
        refine ⟨1308516259657535934341387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3489376692420095824910365 1308516259657535934341387)
        ·
          refine ⟨1962774389486303901512081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308516259657535934341387 1962774389486303901512081)
          ·
            refine ⟨1472080792114727926134061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1962774389486303901512081 1472080792114727926134061)
            ·
              refine ⟨552030297043022972300273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1472080792114727926134061 552030297043022972300273)
              ·
                refine ⟨414022722782267229225205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552030297043022972300273 414022722782267229225205)
                ·
                  refine ⟨38814630260837552739863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414022722782267229225205 38814630260837552739863)
                  ·
                    rfl

theorem cell23_680321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 5].length) (baseStart_680321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680321 prefixEnd_680321 := by exact prefixLift 680321
  have htrace : WordTrace (prefixWord ++ tailWord_680321) baseStart_680321 baseEnd_680321 := by
    simpa [prefixWord, tailWord_680321, baseEnd_680321] using wordTrace_append hprefix tailTrace_680321
  have hstable : (prefixWord ++ tailWord_680321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680321).length < 2 ^ (prefixWord ++ tailWord_680321).sum := by decide
  have hdescent : baseEnd_680321 < baseStart_680321 := by decide
  rcases family_descends (prefixWord ++ tailWord_680321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680354 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_680354 : Nat := 118140960795 + 680354 * 2 ^ 59
def prefixEnd_680354 : Nat := 4983230072969 + 3 ^ 40 * 680354 * 2
def baseEnd_680354 : Nat := 349348617209136345546115

theorem tailTrace_680354 : CollatzResearch.WordTrace tailWord_680354 prefixEnd_680354 349348617209136345546115 := by
  unfold tailWord_680354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203637244300282014384029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16543032651467418705024077 6203637244300282014384029)
  ·
    refine ⟨2326363966612605755394011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6203637244300282014384029 2326363966612605755394011)
    ·
      refine ⟨3489545949918908633091017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326363966612605755394011 3489545949918908633091017)
      ·
        refine ⟨2617159462439181474818263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3489545949918908633091017 2617159462439181474818263)
        ·
          refine ⟨3925739193658772212227395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617159462439181474818263 3925739193658772212227395)
          ·
            refine ⟨5888608790488158318341093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925739193658772212227395 5888608790488158318341093)
            ·
              refine ⟨1104114148216529684688955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5888608790488158318341093 1104114148216529684688955)
              ·
                refine ⟨1656171222324794527033433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104114148216529684688955 1656171222324794527033433)
                ·
                  refine ⟨1242128416743595895275075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1656171222324794527033433 1242128416743595895275075)
                  ·
                    refine ⟨1863192625115393842912613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1242128416743595895275075 1863192625115393842912613)
                    ·
                      refine ⟨349348617209136345546115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1863192625115393842912613 349348617209136345546115)
                      ·
                        rfl

theorem cell23_680354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_680354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680354 prefixEnd_680354 := by exact prefixLift 680354
  have htrace : WordTrace (prefixWord ++ tailWord_680354) baseStart_680354 baseEnd_680354 := by
    simpa [prefixWord, tailWord_680354, baseEnd_680354] using wordTrace_append hprefix tailTrace_680354
  have hstable : (prefixWord ++ tailWord_680354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680354).length < 2 ^ (prefixWord ++ tailWord_680354).sum := by decide
  have hdescent : baseEnd_680354 < baseStart_680354 := by decide
  rcases family_descends (prefixWord ++ tailWord_680354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680364 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_680364 : Nat := 118140960795 + 680364 * 2 ^ 59
def prefixEnd_680364 : Nat := 4983230072969 + 3 ^ 40 * 680364 * 2
def baseEnd_680364 : Nat := 116451250671893768807023

theorem tailTrace_680364 : CollatzResearch.WordTrace tailWord_680364 prefixEnd_680364 116451250671893768807023 := by
  unfold tailWord_680364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407456853582449882700073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16543275804776599843600097 12407456853582449882700073)
  ·
    refine ⟨9305592640186837412025055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12407456853582449882700073 9305592640186837412025055)
    ·
      refine ⟨13958388960280256118037583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9305592640186837412025055 13958388960280256118037583)
      ·
        refine ⟨20937583440420384177056375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13958388960280256118037583 20937583440420384177056375)
        ·
          refine ⟨31406375160630576265584563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20937583440420384177056375 31406375160630576265584563)
          ·
            refine ⟨47109562740945864398376845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31406375160630576265584563 47109562740945864398376845)
            ·
              refine ⟨17666086027854699149391317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47109562740945864398376845 17666086027854699149391317)
              ·
                refine ⟨414048891277844511313859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17666086027854699149391317 414048891277844511313859)
                ·
                  refine ⟨621073336916766766970789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414048891277844511313859 621073336916766766970789)
                  ·
                    refine ⟨116451250671893768807023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621073336916766766970789 116451250671893768807023)
                    ·
                      rfl

theorem cell23_680364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_680364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680364 prefixEnd_680364 := by exact prefixLift 680364
  have htrace : WordTrace (prefixWord ++ tailWord_680364) baseStart_680364 baseEnd_680364 := by
    simpa [prefixWord, tailWord_680364, baseEnd_680364] using wordTrace_append hprefix tailTrace_680364
  have hstable : (prefixWord ++ tailWord_680364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680364).length < 2 ^ (prefixWord ++ tailWord_680364).sum := by decide
  have hdescent : baseEnd_680364 < baseStart_680364 := by decide
  rcases family_descends (prefixWord ++ tailWord_680364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680372 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 5]
def baseStart_680372 : Nat := 118140960795 + 680372 * 2 ^ 59
def prefixEnd_680372 : Nat := 4983230072969 + 3 ^ 40 * 680372 * 2
def baseEnd_680372 : Nat := 38817539984546363902337

theorem tailTrace_680372 : CollatzResearch.WordTrace tailWord_680372 prefixEnd_680372 38817539984546363902337 := by
  unfold tailWord_680372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407602745567958565845685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16543470327423944754460913 12407602745567958565845685)
  ·
    refine ⟨1163212757396996115548033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12407602745567958565845685 1163212757396996115548033)
    ·
      refine ⟨872409568047747086661025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1163212757396996115548033 872409568047747086661025)
      ·
        refine ⟨654307176035810314995769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872409568047747086661025 654307176035810314995769)
        ·
          refine ⟨490730382026857736246827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654307176035810314995769 490730382026857736246827)
          ·
            refine ⟨736095573040286604370241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490730382026857736246827 736095573040286604370241)
            ·
              refine ⟨552071679780214953277681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736095573040286604370241 552071679780214953277681)
              ·
                refine ⟨414053759835161214958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552071679780214953277681 414053759835161214958261)
                ·
                  refine ⟨38817539984546363902337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414053759835161214958261 38817539984546363902337)
                  ·
                    rfl

theorem cell23_680372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_680372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680372 prefixEnd_680372 := by exact prefixLift 680372
  have htrace : WordTrace (prefixWord ++ tailWord_680372) baseStart_680372 baseEnd_680372 := by
    simpa [prefixWord, tailWord_680372, baseEnd_680372] using wordTrace_append hprefix tailTrace_680372
  have hstable : (prefixWord ++ tailWord_680372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680372).length < 2 ^ (prefixWord ++ tailWord_680372).sum := by decide
  have hdescent : baseEnd_680372 < baseStart_680372 := by decide
  rcases family_descends (prefixWord ++ tailWord_680372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680377 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 6]
def baseStart_680377 : Nat := 118140960795 + 680377 * 2 ^ 59
def prefixEnd_680377 : Nat := 4983230072969 + 3 ^ 40 * 680377 * 2
def baseEnd_680377 : Nat := 38817825251576639506501

theorem tailTrace_680377 : CollatzResearch.WordTrace tailWord_680377 prefixEnd_680377 38817825251576639506501 := by
  unfold tailWord_680377
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815387856117802985623385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16543591904078535323748923 24815387856117802985623385)
  ·
    refine ⟨18611540892088352239217539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24815387856117802985623385 18611540892088352239217539)
    ·
      refine ⟨27917311338132528358826309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18611540892088352239217539 27917311338132528358826309)
      ·
        refine ⟨5234495875899849067279933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27917311338132528358826309 5234495875899849067279933)
        ·
          refine ⟨1962935953462443400229975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5234495875899849067279933 1962935953462443400229975)
          ·
            refine ⟨2944403930193665100344963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962935953462443400229975 2944403930193665100344963)
            ·
              refine ⟨4416605895290497650517445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944403930193665100344963 4416605895290497650517445)
              ·
                refine ⟨828113605366968309472021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4416605895290497650517445 828113605366968309472021)
                ·
                  refine ⟨38817825251576639506501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 828113605366968309472021 38817825251576639506501)
                  ·
                    rfl

theorem cell23_680377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_680377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680377 prefixEnd_680377 := by exact prefixLift 680377
  have htrace : WordTrace (prefixWord ++ tailWord_680377) baseStart_680377 baseEnd_680377 := by
    simpa [prefixWord, tailWord_680377, baseEnd_680377] using wordTrace_append hprefix tailTrace_680377
  have hstable : (prefixWord ++ tailWord_680377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680377).length < 2 ^ (prefixWord ++ tailWord_680377).sum := by decide
  have hdescent : baseEnd_680377 < baseStart_680377 := by decide
  rcases family_descends (prefixWord ++ tailWord_680377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680381 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_680381 : Nat := 118140960795 + 680381 * 2 ^ 59
def prefixEnd_680381 : Nat := 4983230072969 + 3 ^ 40 * 680381 * 2
def baseEnd_680381 : Nat := 116454160395602579969497

theorem tailTrace_680381 : CollatzResearch.WordTrace tailWord_680381 prefixEnd_680381 116454160395602579969497 := by
  unfold tailWord_680381
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815533748103311668768997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16543689165402207779179331 24815533748103311668768997)
  ·
    refine ⟨4652912577769370937894187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24815533748103311668768997 4652912577769370937894187)
    ·
      refine ⟨6979368866654056406841281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652912577769370937894187 6979368866654056406841281)
      ·
        refine ⟨5234526649990542305130961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979368866654056406841281 5234526649990542305130961)
        ·
          refine ⟨3925894987492906728848221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234526649990542305130961 3925894987492906728848221)
          ·
            refine ⟨1472210620309840023318083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3925894987492906728848221 1472210620309840023318083)
            ·
              refine ⟨2208315930464760034977125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472210620309840023318083 2208315930464760034977125)
              ·
                refine ⟨414059236962142506558211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2208315930464760034977125 414059236962142506558211)
                ·
                  refine ⟨621088855443213759837317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414059236962142506558211 621088855443213759837317)
                  ·
                    refine ⟨116454160395602579969497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621088855443213759837317 116454160395602579969497)
                    ·
                      rfl

theorem cell23_680381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_680381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680381 prefixEnd_680381 := by exact prefixLift 680381
  have htrace : WordTrace (prefixWord ++ tailWord_680381) baseStart_680381 baseEnd_680381 := by
    simpa [prefixWord, tailWord_680381, baseEnd_680381] using wordTrace_append hprefix tailTrace_680381
  have hstable : (prefixWord ++ tailWord_680381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680381).length < 2 ^ (prefixWord ++ tailWord_680381).sum := by decide
  have hdescent : baseEnd_680381 < baseStart_680381 := by decide
  rcases family_descends (prefixWord ++ tailWord_680381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680424 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_680424 : Nat := 118140960795 + 680424 * 2 ^ 59
def prefixEnd_680424 : Nat := 4983230072969 + 3 ^ 40 * 680424 * 2
def baseEnd_680424 : Nat := 116461520284983690556931

theorem tailTrace_680424 : CollatzResearch.WordTrace tailWord_680424 prefixEnd_680424 116461520284983690556931 := by
  unfold tailWord_680424
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408551043473765006292163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16544734724631686675056217 12408551043473765006292163)
  ·
    refine ⟨18612826565210647509438245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12408551043473765006292163 18612826565210647509438245)
    ·
      refine ⟨3489904980976996408019671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18612826565210647509438245 3489904980976996408019671)
      ·
        refine ⟨5234857471465494612029507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489904980976996408019671 5234857471465494612029507)
        ·
          refine ⟨7852286207198241918044261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234857471465494612029507 7852286207198241918044261)
          ·
            refine ⟨1472303663849670359633299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7852286207198241918044261 1472303663849670359633299)
            ·
              refine ⟨2208455495774505539449949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472303663849670359633299 2208455495774505539449949)
              ·
                refine ⟨828170810915439577293731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2208455495774505539449949 828170810915439577293731)
                ·
                  refine ⟨1242256216373159365940597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828170810915439577293731 1242256216373159365940597)
                  ·
                    refine ⟨116461520284983690556931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1242256216373159365940597 116461520284983690556931)
                    ·
                      rfl

theorem cell23_680424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_680424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680424 prefixEnd_680424 := by exact prefixLift 680424
  have htrace : WordTrace (prefixWord ++ tailWord_680424) baseStart_680424 baseEnd_680424 := by
    simpa [prefixWord, tailWord_680424, baseEnd_680424] using wordTrace_append hprefix tailTrace_680424
  have hstable : (prefixWord ++ tailWord_680424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680424).length < 2 ^ (prefixWord ++ tailWord_680424).sum := by decide
  have hdescent : baseEnd_680424 < baseStart_680424 := by decide
  rcases family_descends (prefixWord ++ tailWord_680424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680438 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_680438 : Nat := 118140960795 + 680438 * 2 ^ 59
def prefixEnd_680438 : Nat := 4983230072969 + 3 ^ 40 * 680438 * 2
def baseEnd_680438 : Nat := 349391749584114016895729

theorem tailTrace_680438 : CollatzResearch.WordTrace tailWord_680438 prefixEnd_680438 349391749584114016895729 := by
  unfold tailWord_680438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551100794306050650224623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16545075139264540269062645 1551100794306050650224623)
  ·
    refine ⟨2326651191459075975336935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551100794306050650224623 2326651191459075975336935)
    ·
      refine ⟨3489976787188613963005403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326651191459075975336935 3489976787188613963005403)
      ·
        refine ⟨5234965180782920944508105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489976787188613963005403 5234965180782920944508105)
        ·
          refine ⟨3926223885587190708381079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234965180782920944508105 3926223885587190708381079)
          ·
            refine ⟨5889335828380786062571619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926223885587190708381079 5889335828380786062571619)
            ·
              refine ⟨8834003742571179093857429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889335828380786062571619 8834003742571179093857429)
              ·
                refine ⟨414093925433024020024567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8834003742571179093857429 414093925433024020024567)
                ·
                  refine ⟨621140888149536030036851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414093925433024020024567 621140888149536030036851)
                  ·
                    refine ⟨931711332224304045055277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621140888149536030036851 931711332224304045055277)
                    ·
                      refine ⟨349391749584114016895729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931711332224304045055277 349391749584114016895729)
                      ·
                        rfl

theorem cell23_680438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_680438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680438 prefixEnd_680438 := by exact prefixLift 680438
  have htrace : WordTrace (prefixWord ++ tailWord_680438) baseStart_680438 baseEnd_680438 := by
    simpa [prefixWord, tailWord_680438, baseEnd_680438] using wordTrace_append hprefix tailTrace_680438
  have hstable : (prefixWord ++ tailWord_680438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680438).length < 2 ^ (prefixWord ++ tailWord_680438).sum := by decide
  have hdescent : baseEnd_680438 < baseStart_680438 := by decide
  rcases family_descends (prefixWord ++ tailWord_680438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680447 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_680447 : Nat := 118140960795 + 680447 * 2 ^ 59
def prefixEnd_680447 : Nat := 4983230072969 + 3 ^ 40 * 680447 * 2
def baseEnd_680447 : Nat := 349396370910004481683187

theorem tailTrace_680447 : CollatzResearch.WordTrace tailWord_680447 prefixEnd_680447 349396370910004481683187 := by
  unfold tailWord_680447
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817940965864204940671595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16545293977242803293781063 24817940965864204940671595)
  ·
    refine ⟨37226911448796307411007393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24817940965864204940671595 37226911448796307411007393)
    ·
      refine ⟨27920183586597230558255545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37226911448796307411007393 27920183586597230558255545)
      ·
        refine ⟨20940137689947922918691659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27920183586597230558255545 20940137689947922918691659)
        ·
          refine ⟨31410206534921884378037489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20940137689947922918691659 31410206534921884378037489)
          ·
            refine ⟨23557654901191413283528117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31410206534921884378037489 23557654901191413283528117)
            ·
              refine ⟨2208530146986694995330761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23557654901191413283528117 2208530146986694995330761)
              ·
                refine ⟨1656397610240021246498071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208530146986694995330761 1656397610240021246498071)
                ·
                  refine ⟨2484596415360031869747107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656397610240021246498071 2484596415360031869747107)
                  ·
                    refine ⟨3726894623040047804620661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484596415360031869747107 3726894623040047804620661)
                    ·
                      refine ⟨349396370910004481683187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3726894623040047804620661 349396370910004481683187)
                      ·
                        rfl

theorem cell23_680447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_680447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680447 prefixEnd_680447 := by exact prefixLift 680447
  have htrace : WordTrace (prefixWord ++ tailWord_680447) baseStart_680447 baseEnd_680447 := by
    simpa [prefixWord, tailWord_680447, baseEnd_680447] using wordTrace_append hprefix tailTrace_680447
  have hstable : (prefixWord ++ tailWord_680447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680447).length < 2 ^ (prefixWord ++ tailWord_680447).sum := by decide
  have hdescent : baseEnd_680447 < baseStart_680447 := by decide
  rcases family_descends (prefixWord ++ tailWord_680447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680457 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_680457 : Nat := 118140960795 + 680457 * 2 ^ 59
def prefixEnd_680457 : Nat := 4983230072969 + 3 ^ 40 * 680457 * 2
def baseEnd_680457 : Nat := 349401505716549442558141

theorem tailTrace_680457 : CollatzResearch.WordTrace tailWord_680457 prefixEnd_680457 349401505716549442558141 := by
  unfold tailWord_680457
  simp only [CollatzResearch.WordTrace]
  refine ⟨24818305695827976648535625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16545537130551984432357083 24818305695827976648535625)
  ·
    refine ⟨18613729271870982486401719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24818305695827976648535625 18613729271870982486401719)
    ·
      refine ⟨27920593907806473729602579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18613729271870982486401719 27920593907806473729602579)
      ·
        refine ⟨41880890861709710594403869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27920593907806473729602579 41880890861709710594403869)
        ·
          refine ⟨15705334073141141472901451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41880890861709710594403869 15705334073141141472901451)
          ·
            refine ⟨23558001109711712209352177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15705334073141141472901451 23558001109711712209352177)
            ·
              refine ⟨17668500832283784157014133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23558001109711712209352177 17668500832283784157014133)
              ·
                refine ⟨1656421953026604764720075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17668500832283784157014133 1656421953026604764720075)
                ·
                  refine ⟨2484632929539907147080113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656421953026604764720075 2484632929539907147080113)
                  ·
                    refine ⟨1863474697154930360310085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2484632929539907147080113 1863474697154930360310085)
                    ·
                      refine ⟨349401505716549442558141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1863474697154930360310085 349401505716549442558141)
                      ·
                        rfl

theorem cell23_680457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_680457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680457 prefixEnd_680457 := by exact prefixLift 680457
  have htrace : WordTrace (prefixWord ++ tailWord_680457) baseStart_680457 baseEnd_680457 := by
    simpa [prefixWord, tailWord_680457, baseEnd_680457] using wordTrace_append hprefix tailTrace_680457
  have hstable : (prefixWord ++ tailWord_680457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680457).length < 2 ^ (prefixWord ++ tailWord_680457).sum := by decide
  have hdescent : baseEnd_680457 < baseStart_680457 := by decide
  rcases family_descends (prefixWord ++ tailWord_680457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680511 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 3]
def baseStart_680511 : Nat := 118140960795 + 680511 * 2 ^ 59
def prefixEnd_680511 : Nat := 4983230072969 + 3 ^ 40 * 680511 * 2
def baseEnd_680511 : Nat := 349429233671892231282893

theorem tailTrace_680511 : CollatzResearch.WordTrace tailWord_680511 prefixEnd_680511 349429233671892231282893 := by
  unfold tailWord_680511
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820275237632343871001387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16546850158421562580667591 24820275237632343871001387)
  ·
    refine ⟨37230412856448515806502081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24820275237632343871001387 37230412856448515806502081)
    ·
      refine ⟨27922809642336386854876561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37230412856448515806502081 27922809642336386854876561)
      ·
        refine ⟨20942107231752290141157421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27922809642336386854876561 20942107231752290141157421)
        ·
          refine ⟨7853290211907108802934033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20942107231752290141157421 7853290211907108802934033)
          ·
            refine ⟨5889967658930331602200525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7853290211907108802934033 5889967658930331602200525)
            ·
              refine ⟨2208737872098874350825197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5889967658930331602200525 2208737872098874350825197)
              ·
                refine ⟨828276702037077881559449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2208737872098874350825197 828276702037077881559449)
                ·
                  refine ⟨621207526527808411169587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 828276702037077881559449 621207526527808411169587)
                  ·
                    refine ⟨931811289791712616754381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621207526527808411169587 931811289791712616754381)
                    ·
                      refine ⟨349429233671892231282893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931811289791712616754381 349429233671892231282893)
                      ·
                        rfl

theorem cell23_680511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_680511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680511 prefixEnd_680511 := by exact prefixLift 680511
  have htrace : WordTrace (prefixWord ++ tailWord_680511) baseStart_680511 baseEnd_680511 := by
    simpa [prefixWord, tailWord_680511, baseEnd_680511] using wordTrace_append hprefix tailTrace_680511
  have hstable : (prefixWord ++ tailWord_680511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680511).length < 2 ^ (prefixWord ++ tailWord_680511).sum := by decide
  have hdescent : baseEnd_680511 < baseStart_680511 := by decide
  rcases family_descends (prefixWord ++ tailWord_680511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680546 : List Nat := [3, 3, 2, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_680546 : Nat := 118140960795 + 680546 * 2 ^ 59
def prefixEnd_680546 : Nat := 4983230072969 + 3 ^ 40 * 680546 * 2
def baseEnd_680546 : Nat := 349447205494799594345233

theorem tailTrace_680546 : CollatzResearch.WordTrace tailWord_680546 prefixEnd_680546 349447205494799594345233 := by
  unfold tailWord_680546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205387948126386212131373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16547701195003696565683661 6205387948126386212131373)
  ·
    refine ⟨2327020480547394829549265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6205387948126386212131373 2327020480547394829549265)
    ·
      refine ⟨1745265360410546122161949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2327020480547394829549265 1745265360410546122161949)
      ·
        refine ⟨654474510153954795810731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1745265360410546122161949 654474510153954795810731)
        ·
          refine ⟨981711765230932193716097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654474510153954795810731 981711765230932193716097)
          ·
            refine ⟨736283823923199145287073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981711765230932193716097 736283823923199145287073)
            ·
              refine ⟨552212867942399358965305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736283823923199145287073 552212867942399358965305)
              ·
                refine ⟨414159650956799519223979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552212867942399358965305 414159650956799519223979)
                ·
                  refine ⟨621239476435199278835969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414159650956799519223979 621239476435199278835969)
                  ·
                    refine ⟨465929607326399459126977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 621239476435199278835969 465929607326399459126977)
                    ·
                      refine ⟨349447205494799594345233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 465929607326399459126977 349447205494799594345233)
                      ·
                        rfl

theorem cell23_680546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_680546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680546 prefixEnd_680546 := by exact prefixLift 680546
  have htrace : WordTrace (prefixWord ++ tailWord_680546) baseStart_680546 baseEnd_680546 := by
    simpa [prefixWord, tailWord_680546, baseEnd_680546] using wordTrace_append hprefix tailTrace_680546
  have hstable : (prefixWord ++ tailWord_680546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680546).length < 2 ^ (prefixWord ++ tailWord_680546).sum := by decide
  have hdescent : baseEnd_680546 < baseStart_680546 := by decide
  rcases family_descends (prefixWord ++ tailWord_680546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680554 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_680554 : Nat := 118140960795 + 680554 * 2 ^ 59
def prefixEnd_680554 : Nat := 4983230072969 + 3 ^ 40 * 680554 * 2
def baseEnd_680554 : Nat := 349451313340035563045195

theorem tailTrace_680554 : CollatzResearch.WordTrace tailWord_680554 prefixEnd_680554 349451313340035563045195 := by
  unfold tailWord_680554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205460894119140553704179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16547895717651041476544477 6205460894119140553704179)
  ·
    refine ⟨9308191341178710830556269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6205460894119140553704179 9308191341178710830556269)
    ·
      refine ⟨3490571752942016561458601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9308191341178710830556269 3490571752942016561458601)
      ·
        refine ⟨2617928814706512421093951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3490571752942016561458601 2617928814706512421093951)
        ·
          refine ⟨3926893222059768631640927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617928814706512421093951 3926893222059768631640927)
          ·
            refine ⟨5890339833089652947461391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926893222059768631640927 5890339833089652947461391)
            ·
              refine ⟨8835509749634479421192087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890339833089652947461391 8835509749634479421192087)
              ·
                refine ⟨13253264624451719131788131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8835509749634479421192087 13253264624451719131788131)
                ·
                  refine ⟨19879896936677578697682197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13253264624451719131788131 19879896936677578697682197)
                  ·
                    refine ⟨931870168906761501453853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19879896936677578697682197 931870168906761501453853)
                    ·
                      refine ⟨349451313340035563045195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 931870168906761501453853 349451313340035563045195)
                      ·
                        rfl

theorem cell23_680554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_680554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680554 prefixEnd_680554 := by exact prefixLift 680554
  have htrace : WordTrace (prefixWord ++ tailWord_680554) baseStart_680554 baseEnd_680554 := by
    simpa [prefixWord, tailWord_680554, baseEnd_680554] using wordTrace_append hprefix tailTrace_680554
  have hstable : (prefixWord ++ tailWord_680554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680554).length < 2 ^ (prefixWord ++ tailWord_680554).sum := by decide
  have hdescent : baseEnd_680554 < baseStart_680554 := by decide
  rcases family_descends (prefixWord ++ tailWord_680554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680617 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_680617 : Nat := 118140960795 + 680617 * 2 ^ 59
def prefixEnd_680617 : Nat := 4983230072969 + 3 ^ 40 * 680617 * 2
def baseEnd_680617 : Nat := 116494554207089605519135

theorem tailTrace_680617 : CollatzResearch.WordTrace tailWord_680617 prefixEnd_680617 116494554207089605519135 := by
  unfold tailWord_680617
  simp only [CollatzResearch.WordTrace]
  refine ⟨24824141375248323974360105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16549427583498882649573403 24824141375248323974360105)
  ·
    refine ⟨18618106031436242980770079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24824141375248323974360105 18618106031436242980770079)
    ·
      refine ⟨27927159047154364471155119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18618106031436242980770079 27927159047154364471155119)
      ·
        refine ⟨41890738570731546706732679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27927159047154364471155119 41890738570731546706732679)
        ·
          refine ⟨62836107856097320060099019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41890738570731546706732679 62836107856097320060099019)
          ·
            refine ⟨94254161784145980090148529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62836107856097320060099019 94254161784145980090148529)
            ·
              refine ⟨70690621338109485067611397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94254161784145980090148529 70690621338109485067611397)
              ·
                refine ⟨13254491500895528450177137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70690621338109485067611397 13254491500895528450177137)
                ·
                  refine ⟨9940868625671646337632853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13254491500895528450177137 9940868625671646337632853)
                  ·
                    refine ⟨116494554207089605519135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9940868625671646337632853 116494554207089605519135)
                    ·
                      rfl

theorem cell23_680617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_680617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680617 prefixEnd_680617 := by exact prefixLift 680617
  have htrace : WordTrace (prefixWord ++ tailWord_680617) baseStart_680617 baseEnd_680617 := by
    simpa [prefixWord, tailWord_680617, baseEnd_680617] using wordTrace_append hprefix tailTrace_680617
  have hstable : (prefixWord ++ tailWord_680617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680617).length < 2 ^ (prefixWord ++ tailWord_680617).sum := by decide
  have hdescent : baseEnd_680617 < baseStart_680617 := by decide
  rcases family_descends (prefixWord ++ tailWord_680617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680658 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_680658 : Nat := 118140960795 + 680658 * 2 ^ 59
def prefixEnd_680658 : Nat := 4983230072969 + 3 ^ 40 * 680658 * 2
def baseEnd_680658 : Nat := 349504715328103156144717

theorem tailTrace_680658 : CollatzResearch.WordTrace tailWord_680658 prefixEnd_680658 349504715328103156144717 := by
  unfold tailWord_680658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206409192024946994150657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16550424512066525317735085 6206409192024946994150657)
  ·
    refine ⟨4654806894018710245612993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6206409192024946994150657 4654806894018710245612993)
    ·
      refine ⟨3491105170514032684209745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4654806894018710245612993 3491105170514032684209745)
      ·
        refine ⟨2618328877885524513157309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3491105170514032684209745 2618328877885524513157309)
        ·
          refine ⟨981873329207071692433991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2618328877885524513157309 981873329207071692433991)
          ·
            refine ⟨1472809993810607538650987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981873329207071692433991 1472809993810607538650987)
            ·
              refine ⟨2209214990715911307976481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472809993810607538650987 2209214990715911307976481)
              ·
                refine ⟨1656911243036933480982361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209214990715911307976481 1656911243036933480982361)
                ·
                  refine ⟨1242683432277700110736771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1656911243036933480982361 1242683432277700110736771)
                  ·
                    refine ⟨1864025148416550166105157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1242683432277700110736771 1864025148416550166105157)
                    ·
                      refine ⟨349504715328103156144717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1864025148416550166105157 349504715328103156144717)
                      ·
                        rfl

theorem cell23_680658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_680658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680658 prefixEnd_680658 := by exact prefixLift 680658
  have htrace : WordTrace (prefixWord ++ tailWord_680658) baseStart_680658 baseEnd_680658 := by
    simpa [prefixWord, tailWord_680658, baseEnd_680658] using wordTrace_append hprefix tailTrace_680658
  have hstable : (prefixWord ++ tailWord_680658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680658).length < 2 ^ (prefixWord ++ tailWord_680658).sum := by decide
  have hdescent : baseEnd_680658 < baseStart_680658 := by decide
  rcases family_descends (prefixWord ++ tailWord_680658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680664 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 8]
def baseStart_680664 : Nat := 118140960795 + 680664 * 2 ^ 59
def prefixEnd_680664 : Nat := 4983230072969 + 3 ^ 40 * 680664 * 2
def baseEnd_680664 : Nat := 38834199579114459185521

theorem tailTrace_680664 : CollatzResearch.WordTrace tailWord_680664 prefixEnd_680664 38834199579114459185521 := by
  unfold tailWord_680664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412927803039025500660523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16550570404052034000880697 12412927803039025500660523)
  ·
    refine ⟨18619391704558538250990785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12412927803039025500660523 18619391704558538250990785)
    ·
      refine ⟨13964543778418903688243089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18619391704558538250990785 13964543778418903688243089)
      ·
        refine ⟨10473407833814177766182317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13964543778418903688243089 10473407833814177766182317)
        ·
          refine ⟨3927527937680316662318369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10473407833814177766182317 3927527937680316662318369)
          ·
            refine ⟨2945645953260237496738777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3927527937680316662318369 2945645953260237496738777)
            ·
              refine ⟨2209234464945178122554083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945645953260237496738777 2209234464945178122554083)
              ·
                refine ⟨3313851697417767183831125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209234464945178122554083 3313851697417767183831125)
                ·
                  refine ⟨38834199579114459185521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3313851697417767183831125 38834199579114459185521)
                  ·
                    rfl

theorem cell23_680664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_680664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680664 prefixEnd_680664 := by exact prefixLift 680664
  have htrace : WordTrace (prefixWord ++ tailWord_680664) baseStart_680664 baseEnd_680664 := by
    simpa [prefixWord, tailWord_680664, baseEnd_680664] using wordTrace_append hprefix tailTrace_680664
  have hstable : (prefixWord ++ tailWord_680664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680664).length < 2 ^ (prefixWord ++ tailWord_680664).sum := by decide
  have hdescent : baseEnd_680664 < baseStart_680664 := by decide
  rcases family_descends (prefixWord ++ tailWord_680664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680681 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 6]
def baseStart_680681 : Nat := 118140960795 + 680681 * 2 ^ 59
def prefixEnd_680681 : Nat := 4983230072969 + 3 ^ 40 * 680681 * 2
def baseEnd_680681 : Nat := 38835169487017396239679

theorem tailTrace_680681 : CollatzResearch.WordTrace tailWord_680681 prefixEnd_680681 38835169487017396239679 := by
  unfold tailWord_680681
  simp only [CollatzResearch.WordTrace]
  refine ⟨24826475647016462904689897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16550983764677641936459931 24826475647016462904689897)
  ·
    refine ⟨18619856735262347178517423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24826475647016462904689897 18619856735262347178517423)
    ·
      refine ⟨27929785102893520767776135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18619856735262347178517423 27929785102893520767776135)
      ·
        refine ⟨41894677654340281151664203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27929785102893520767776135 41894677654340281151664203)
        ·
          refine ⟨62842016481510421727496305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41894677654340281151664203 62842016481510421727496305)
          ·
            refine ⟨47131512361132816295622229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62842016481510421727496305 47131512361132816295622229)
            ·
              refine ⟨552322410482025190964323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 47131512361132816295622229 552322410482025190964323)
              ·
                refine ⟨828483615723037786446485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552322410482025190964323 828483615723037786446485)
                ·
                  refine ⟨38835169487017396239679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 828483615723037786446485 38835169487017396239679)
                  ·
                    rfl

theorem cell23_680681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 6].length) (baseStart_680681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680681 prefixEnd_680681 := by exact prefixLift 680681
  have htrace : WordTrace (prefixWord ++ tailWord_680681) baseStart_680681 baseEnd_680681 := by
    simpa [prefixWord, tailWord_680681, baseEnd_680681] using wordTrace_append hprefix tailTrace_680681
  have hstable : (prefixWord ++ tailWord_680681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680681).length < 2 ^ (prefixWord ++ tailWord_680681).sum := by decide
  have hdescent : baseEnd_680681 < baseStart_680681 := by decide
  rcases family_descends (prefixWord ++ tailWord_680681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680691 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 3]
def baseStart_680691 : Nat := 118140960795 + 680691 * 2 ^ 59
def prefixEnd_680691 : Nat := 4983230072969 + 3 ^ 40 * 680691 * 2
def baseEnd_680691 : Nat := 349521660189701527032065

theorem tailTrace_680691 : CollatzResearch.WordTrace tailWord_680691 prefixEnd_680691 349521660189701527032065 := by
  unfold tailWord_680691
  simp only [CollatzResearch.WordTrace]
  refine ⟨24826840376980234612553927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16551226917986823075035951 24826840376980234612553927)
  ·
    refine ⟨37240260565470351918830891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24826840376980234612553927 37240260565470351918830891)
    ·
      refine ⟨55860390848205527878246337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37240260565470351918830891 55860390848205527878246337)
      ·
        refine ⟨41895293136154145908684753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55860390848205527878246337 41895293136154145908684753)
        ·
          refine ⟨31421469852115609431513565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41895293136154145908684753 31421469852115609431513565)
          ·
            refine ⟨11783051194543353536817587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31421469852115609431513565 11783051194543353536817587)
            ·
              refine ⟨17674576791815030305226381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11783051194543353536817587 17674576791815030305226381)
              ·
                refine ⟨6627966296930636364459893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17674576791815030305226381 6627966296930636364459893)
                ·
                  refine ⟨621371840337247159168115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6627966296930636364459893 621371840337247159168115)
                  ·
                    refine ⟨932057760505870738752173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621371840337247159168115 932057760505870738752173)
                    ·
                      refine ⟨349521660189701527032065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932057760505870738752173 349521660189701527032065)
                      ·
                        rfl

theorem cell23_680691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_680691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680691 prefixEnd_680691 := by exact prefixLift 680691
  have htrace : WordTrace (prefixWord ++ tailWord_680691) baseStart_680691 baseEnd_680691 := by
    simpa [prefixWord, tailWord_680691, baseEnd_680691] using wordTrace_append hprefix tailTrace_680691
  have hstable : (prefixWord ++ tailWord_680691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680691).length < 2 ^ (prefixWord ++ tailWord_680691).sum := by decide
  have hdescent : baseEnd_680691 < baseStart_680691 := by decide
  rcases family_descends (prefixWord ++ tailWord_680691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680692 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_680692 : Nat := 118140960795 + 680692 * 2 ^ 59
def prefixEnd_680692 : Nat := 4983230072969 + 3 ^ 40 * 680692 * 2
def baseEnd_680692 : Nat := 349522173670356023119561

theorem tailTrace_680692 : CollatzResearch.WordTrace tailWord_680692 prefixEnd_680692 349522173670356023119561 := by
  unfold tailWord_680692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413438424988305891670165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16551251233317741188893553 12413438424988305891670165)
  ·
    refine ⟨581879926171326838672039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12413438424988305891670165 581879926171326838672039)
    ·
      refine ⟨872819889256990258008059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581879926171326838672039 872819889256990258008059)
      ·
        refine ⟨1309229833885485387012089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872819889256990258008059 1309229833885485387012089)
        ·
          refine ⟨981922375414114040259067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309229833885485387012089 981922375414114040259067)
          ·
            refine ⟨1472883563121171060388601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981922375414114040259067 1472883563121171060388601)
            ·
              refine ⟨1104662672340878295291451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472883563121171060388601 1104662672340878295291451)
              ·
                refine ⟨1656994008511317442937177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104662672340878295291451 1656994008511317442937177)
                ·
                  refine ⟨1242745506383488082202883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1656994008511317442937177 1242745506383488082202883)
                  ·
                    refine ⟨1864118259575232123304325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1242745506383488082202883 1864118259575232123304325)
                    ·
                      refine ⟨349522173670356023119561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1864118259575232123304325 349522173670356023119561)
                      ·
                        rfl

theorem cell23_680692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_680692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680692 prefixEnd_680692 := by exact prefixLift 680692
  have htrace : WordTrace (prefixWord ++ tailWord_680692) baseStart_680692 baseEnd_680692 := by
    simpa [prefixWord, tailWord_680692, baseEnd_680692] using wordTrace_append hprefix tailTrace_680692
  have hstable : (prefixWord ++ tailWord_680692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680692).length < 2 ^ (prefixWord ++ tailWord_680692).sum := by decide
  have hdescent : baseEnd_680692 < baseStart_680692 := by decide
  rcases family_descends (prefixWord ++ tailWord_680692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680725 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_680725 : Nat := 118140960795 + 680725 * 2 ^ 59
def prefixEnd_680725 : Nat := 4983230072969 + 3 ^ 40 * 680725 * 2
def baseEnd_680725 : Nat := 349539118531954394006909

theorem tailTrace_680725 : CollatzResearch.WordTrace tailWord_680725 prefixEnd_680725 349539118531954394006909 := by
  unfold tailWord_680725
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828080458857058419291629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16552053639238038946194419 24828080458857058419291629)
  ·
    refine ⟨9310530172071396907234361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24828080458857058419291629 9310530172071396907234361)
    ·
      refine ⟨6982897629053547680425771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9310530172071396907234361 6982897629053547680425771)
      ·
        refine ⟨10474346443580321520638657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982897629053547680425771 10474346443580321520638657)
        ·
          refine ⟨7855759832685241140478993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10474346443580321520638657 7855759832685241140478993)
          ·
            refine ⟨5891819874513930855359245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855759832685241140478993 5891819874513930855359245)
            ·
              refine ⟨2209432452942724070759717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5891819874513930855359245 2209432452942724070759717)
              ·
                refine ⟨414268584926760763267447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2209432452942724070759717 414268584926760763267447)
                ·
                  refine ⟨621402877390141144901171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414268584926760763267447 621402877390141144901171)
                  ·
                    refine ⟨932104316085211717351757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621402877390141144901171 932104316085211717351757)
                    ·
                      refine ⟨349539118531954394006909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932104316085211717351757 349539118531954394006909)
                      ·
                        rfl

theorem cell23_680725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_680725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680725 prefixEnd_680725 := by exact prefixLift 680725
  have htrace : WordTrace (prefixWord ++ tailWord_680725) baseStart_680725 baseEnd_680725 := by
    simpa [prefixWord, tailWord_680725, baseEnd_680725] using wordTrace_append hprefix tailTrace_680725
  have hstable : (prefixWord ++ tailWord_680725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680725).length < 2 ^ (prefixWord ++ tailWord_680725).sum := by decide
  have hdescent : baseEnd_680725 < baseStart_680725 := by decide
  rcases family_descends (prefixWord ++ tailWord_680725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680741 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_680741 : Nat := 118140960795 + 680741 * 2 ^ 59
def prefixEnd_680741 : Nat := 4983230072969 + 3 ^ 40 * 680741 * 2
def baseEnd_680741 : Nat := 116515778074142110468945

theorem tailTrace_680741 : CollatzResearch.WordTrace tailWord_680741 prefixEnd_680741 116515778074142110468945 := by
  unfold tailWord_680741
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828664026799093151874077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16552442684532728767916051 24828664026799093151874077)
  ·
    refine ⟨9310749010049659931952779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24828664026799093151874077 9310749010049659931952779)
    ·
      refine ⟨13966123515074489897929169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9310749010049659931952779 13966123515074489897929169)
      ·
        refine ⟨10474592636305867423446877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13966123515074489897929169 10474592636305867423446877)
        ·
          refine ⟨3927972238614700283792579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10474592636305867423446877 3927972238614700283792579)
          ·
            refine ⟨5891958357922050425688869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927972238614700283792579 5891958357922050425688869)
            ·
              refine ⟨1104742192110384454816663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5891958357922050425688869 1104742192110384454816663)
              ·
                refine ⟨1657113288165576682224995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104742192110384454816663 1657113288165576682224995)
                ·
                  refine ⟨2485669932248365023337493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657113288165576682224995 2485669932248365023337493)
                  ·
                    refine ⟨116515778074142110468945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2485669932248365023337493 116515778074142110468945)
                    ·
                      rfl

theorem cell23_680741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_680741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680741 prefixEnd_680741 := by exact prefixLift 680741
  have htrace : WordTrace (prefixWord ++ tailWord_680741) baseStart_680741 baseEnd_680741 := by
    simpa [prefixWord, tailWord_680741, baseEnd_680741] using wordTrace_append hprefix tailTrace_680741
  have hstable : (prefixWord ++ tailWord_680741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680741).length < 2 ^ (prefixWord ++ tailWord_680741).sum := by decide
  have hdescent : baseEnd_680741 < baseStart_680741 := by decide
  rcases family_descends (prefixWord ++ tailWord_680741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680762 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_680762 : Nat := 118140960795 + 680762 * 2 ^ 59
def prefixEnd_680762 : Nat := 4983230072969 + 3 ^ 40 * 680762 * 2
def baseEnd_680762 : Nat := 116519372438723583081413

theorem tailTrace_680762 : CollatzResearch.WordTrace tailWord_680762 prefixEnd_680762 116519372438723583081413 := by
  unfold tailWord_680762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207357489930753434597135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16552953306482009158925693 6207357489930753434597135)
  ·
    refine ⟨9311036234896130151895703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6207357489930753434597135 9311036234896130151895703)
    ·
      refine ⟨13966554352344195227843555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9311036234896130151895703 13966554352344195227843555)
      ·
        refine ⟨20949831528516292841765333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13966554352344195227843555 20949831528516292841765333)
        ·
          refine ⟨491011676449600613478875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20949831528516292841765333 491011676449600613478875)
          ·
            refine ⟨736517514674400920218313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491011676449600613478875 736517514674400920218313)
            ·
              refine ⟨552388136005800690163735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736517514674400920218313 552388136005800690163735)
              ·
                refine ⟨828582204008701035245603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552388136005800690163735 828582204008701035245603)
                ·
                  refine ⟨1242873306013051552868405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828582204008701035245603 1242873306013051552868405)
                  ·
                    refine ⟨116519372438723583081413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1242873306013051552868405 116519372438723583081413)
                    ·
                      rfl

theorem cell23_680762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_680762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680762 prefixEnd_680762 := by exact prefixLift 680762
  have htrace : WordTrace (prefixWord ++ tailWord_680762) baseStart_680762 baseEnd_680762 := by
    simpa [prefixWord, tailWord_680762, baseEnd_680762] using wordTrace_append hprefix tailTrace_680762
  have hstable : (prefixWord ++ tailWord_680762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680762).length < 2 ^ (prefixWord ++ tailWord_680762).sum := by decide
  have hdescent : baseEnd_680762 < baseStart_680762 := by decide
  rcases family_descends (prefixWord ++ tailWord_680762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680765 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_680765 : Nat := 118140960795 + 680765 * 2 ^ 59
def prefixEnd_680765 : Nat := 4983230072969 + 3 ^ 40 * 680765 * 2
def baseEnd_680765 : Nat := 349559657758134237506725

theorem tailTrace_680765 : CollatzResearch.WordTrace tailWord_680765 prefixEnd_680765 349559657758134237506725 := by
  unfold tailWord_680765
  simp only [CollatzResearch.WordTrace]
  refine ⟨24829539378712145250747749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16553026252474763500498499 24829539378712145250747749)
  ·
    refine ⟨4655538633508527234515203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24829539378712145250747749 4655538633508527234515203)
    ·
      refine ⟨6983307950262790851772805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4655538633508527234515203 6983307950262790851772805)
      ·
        refine ⟨1309370240674273284707401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6983307950262790851772805 1309370240674273284707401)
        ·
          refine ⟨982027680505704963530551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309370240674273284707401 982027680505704963530551)
          ·
            refine ⟨1473041520758557445295827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982027680505704963530551 1473041520758557445295827)
            ·
              refine ⟨2209562281137836167943741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473041520758557445295827 2209562281137836167943741)
              ·
                refine ⟨828585855426688562978903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209562281137836167943741 828585855426688562978903)
                ·
                  refine ⟨1242878783140032844468355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828585855426688562978903 1242878783140032844468355)
                  ·
                    refine ⟨1864318174710049266702533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1242878783140032844468355 1864318174710049266702533)
                    ·
                      refine ⟨349559657758134237506725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1864318174710049266702533 349559657758134237506725)
                      ·
                        rfl

theorem cell23_680765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_680765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680765 prefixEnd_680765 := by exact prefixLift 680765
  have htrace : WordTrace (prefixWord ++ tailWord_680765) baseStart_680765 baseEnd_680765 := by
    simpa [prefixWord, tailWord_680765, baseEnd_680765] using wordTrace_append hprefix tailTrace_680765
  have hstable : (prefixWord ++ tailWord_680765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680765).length < 2 ^ (prefixWord ++ tailWord_680765).sum := by decide
  have hdescent : baseEnd_680765 < baseStart_680765 := by decide
  rcases family_descends (prefixWord ++ tailWord_680765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680784 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_680784 : Nat := 118140960795 + 680784 * 2 ^ 59
def prefixEnd_680784 : Nat := 4983230072969 + 3 ^ 40 * 680784 * 2
def baseEnd_680784 : Nat := 116523137963523221056379

theorem tailTrace_680784 : CollatzResearch.WordTrace tailWord_680784 prefixEnd_680784 116523137963523221056379 := by
  unfold tailWord_680784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415116182821655747844703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16553488243762207663792937 12415116182821655747844703)
  ·
    refine ⟨18622674274232483621767055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12415116182821655747844703 18622674274232483621767055)
    ·
      refine ⟨27934011411348725432650583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18622674274232483621767055 27934011411348725432650583)
      ·
        refine ⟨41901017117023088148975875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27934011411348725432650583 41901017117023088148975875)
        ·
          refine ⟨62851525675534632223463813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41901017117023088148975875 62851525675534632223463813)
          ·
            refine ⟨11784661064162743541899465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62851525675534632223463813 11784661064162743541899465)
            ·
              refine ⟨8838495798122057656424599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11784661064162743541899465 8838495798122057656424599)
              ·
                refine ⟨13257743697183086484636899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8838495798122057656424599 13257743697183086484636899)
                ·
                  refine ⟨19886615545774629726955349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13257743697183086484636899 19886615545774629726955349)
                  ·
                    refine ⟨116523137963523221056379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19886615545774629726955349 116523137963523221056379)
                    ·
                      rfl

theorem cell23_680784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_680784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680784 prefixEnd_680784 := by exact prefixLift 680784
  have htrace : WordTrace (prefixWord ++ tailWord_680784) baseStart_680784 baseEnd_680784 := by
    simpa [prefixWord, tailWord_680784, baseEnd_680784] using wordTrace_append hprefix tailTrace_680784
  have hstable : (prefixWord ++ tailWord_680784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680784).length < 2 ^ (prefixWord ++ tailWord_680784).sum := by decide
  have hdescent : baseEnd_680784 < baseStart_680784 := by decide
  rcases family_descends (prefixWord ++ tailWord_680784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680802 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_680802 : Nat := 118140960795 + 680802 * 2 ^ 59
def prefixEnd_680802 : Nat := 4983230072969 + 3 ^ 40 * 680802 * 2
def baseEnd_680802 : Nat := 349578656542350592744055

theorem tailTrace_680802 : CollatzResearch.WordTrace tailWord_680802 prefixEnd_680802 349578656542350592744055 := by
  unfold tailWord_680802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207722219894525142461165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16553925919718733713229773 6207722219894525142461165)
  ·
    refine ⟨2327895832460446928422937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6207722219894525142461165 2327895832460446928422937)
    ·
      refine ⟨1745921874345335196317203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2327895832460446928422937 1745921874345335196317203)
      ·
        refine ⟨2618882811518002794475805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745921874345335196317203 2618882811518002794475805)
        ·
          refine ⟨982081054319251047928427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2618882811518002794475805 982081054319251047928427)
          ·
            refine ⟨1473121581478876571892641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982081054319251047928427 1473121581478876571892641)
            ·
              refine ⟨1104841186109157428919481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473121581478876571892641 1104841186109157428919481)
              ·
                refine ⟨828630889581868071689611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104841186109157428919481 828630889581868071689611)
                ·
                  refine ⟨1242946334372802107534417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828630889581868071689611 1242946334372802107534417)
                  ·
                    refine ⟨932209750779601580650813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1242946334372802107534417 932209750779601580650813)
                    ·
                      refine ⟨349578656542350592744055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932209750779601580650813 349578656542350592744055)
                      ·
                        rfl

theorem cell23_680802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_680802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680802 prefixEnd_680802 := by exact prefixLift 680802
  have htrace : WordTrace (prefixWord ++ tailWord_680802) baseStart_680802 baseEnd_680802 := by
    simpa [prefixWord, tailWord_680802, baseEnd_680802] using wordTrace_append hprefix tailTrace_680802
  have hstable : (prefixWord ++ tailWord_680802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680802).length < 2 ^ (prefixWord ++ tailWord_680802).sum := by decide
  have hdescent : baseEnd_680802 < baseStart_680802 := by decide
  rcases family_descends (prefixWord ++ tailWord_680802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680825 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 1, 3, 2]
def baseStart_680825 : Nat := 118140960795 + 680825 * 2 ^ 59
def prefixEnd_680825 : Nat := 4983230072969 + 3 ^ 40 * 680825 * 2
def baseEnd_680825 : Nat := 349590466597404002756449

theorem tailTrace_680825 : CollatzResearch.WordTrace tailWord_680825 prefixEnd_680825 349590466597404002756449 := by
  unfold tailWord_680825
  simp only [CollatzResearch.WordTrace]
  refine ⟨24831727758494775497931929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16554485172329850331954619 24831727758494775497931929)
  ·
    refine ⟨18623795818871081623448947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24831727758494775497931929 18623795818871081623448947)
    ·
      refine ⟨27935693728306622435173421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18623795818871081623448947 27935693728306622435173421)
      ·
        refine ⟨10475885148114983413190033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27935693728306622435173421 10475885148114983413190033)
        ·
          refine ⟨7856913861086237559892525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10475885148114983413190033 7856913861086237559892525)
          ·
            refine ⟨2946342697907339084959697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7856913861086237559892525 2946342697907339084959697)
            ·
              refine ⟨2209757023430504313719773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946342697907339084959697 2209757023430504313719773)
              ·
                refine ⟨828658883786439117644915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209757023430504313719773 828658883786439117644915)
                ·
                  refine ⟨1242988325679658676467373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828658883786439117644915 1242988325679658676467373)
                  ·
                    refine ⟨466120622129872003675265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1242988325679658676467373 466120622129872003675265)
                    ·
                      refine ⟨349590466597404002756449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 466120622129872003675265 349590466597404002756449)
                      ·
                        rfl

theorem cell23_680825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_680825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680825 prefixEnd_680825 := by exact prefixLift 680825
  have htrace : WordTrace (prefixWord ++ tailWord_680825) baseStart_680825 baseEnd_680825 := by
    simpa [prefixWord, tailWord_680825, baseEnd_680825] using wordTrace_append hprefix tailTrace_680825
  have hstable : (prefixWord ++ tailWord_680825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680825).length < 2 ^ (prefixWord ++ tailWord_680825).sum := by decide
  have hdescent : baseEnd_680825 < baseStart_680825 := by decide
  rcases family_descends (prefixWord ++ tailWord_680825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680861 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 9]
def baseStart_680861 : Nat := 118140960795 + 680861 * 2 ^ 59
def prefixEnd_680861 : Nat := 4983230072969 + 3 ^ 40 * 680861 * 2
def baseEnd_680861 : Nat := 38845439100107317989587

theorem tailTrace_680861 : CollatzResearch.WordTrace tailWord_680861 prefixEnd_680861 38845439100107317989587 := by
  unfold tailWord_680861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24833040786364353646242437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16555360524242902430828291 24833040786364353646242437)
  ·
    refine ⟨4656195147443316308670457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24833040786364353646242437 4656195147443316308670457)
    ·
      refine ⟨3492146360582487231502843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4656195147443316308670457 3492146360582487231502843)
      ·
        refine ⟨5238219540873730847254265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492146360582487231502843 5238219540873730847254265)
        ·
          refine ⟨3928664655655298135440699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238219540873730847254265 3928664655655298135440699)
          ·
            refine ⟨5892996983482947203161049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928664655655298135440699 5892996983482947203161049)
            ·
              refine ⟨4419747737612210402370787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5892996983482947203161049 4419747737612210402370787)
              ·
                refine ⟨6629621606418315603556181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419747737612210402370787 6629621606418315603556181)
                ·
                  refine ⟨38845439100107317989587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6629621606418315603556181 38845439100107317989587)
                  ·
                    rfl

theorem cell23_680861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_680861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680861 prefixEnd_680861 := by exact prefixLift 680861
  have htrace : WordTrace (prefixWord ++ tailWord_680861) baseStart_680861 baseEnd_680861 := by
    simpa [prefixWord, tailWord_680861, baseEnd_680861] using wordTrace_append hprefix tailTrace_680861
  have hstable : (prefixWord ++ tailWord_680861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680861).length < 2 ^ (prefixWord ++ tailWord_680861).sum := by decide
  have hdescent : baseEnd_680861 < baseStart_680861 := by decide
  rcases family_descends (prefixWord ++ tailWord_680861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680925 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_680925 : Nat := 118140960795 + 680925 * 2 ^ 59
def prefixEnd_680925 : Nat := 4983230072969 + 3 ^ 40 * 680925 * 2
def baseEnd_680925 : Nat := 116547271554284537168663

theorem tailTrace_680925 : CollatzResearch.WordTrace tailWord_680925 prefixEnd_680925 116547271554284537168663 := by
  unfold tailWord_680925
  simp only [CollatzResearch.WordTrace]
  refine ⟨24835375058132492576572229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16556916705421661717714819 24835375058132492576572229)
  ·
    refine ⟨4656632823399842358107293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24835375058132492576572229 4656632823399842358107293)
    ·
      refine ⟨1746237308774940884290235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4656632823399842358107293 1746237308774940884290235)
      ·
        refine ⟨2619355963162411326435353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746237308774940884290235 2619355963162411326435353)
        ·
          refine ⟨1964516972371808494826515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619355963162411326435353 1964516972371808494826515)
          ·
            refine ⟨2946775458557712742239773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964516972371808494826515 2946775458557712742239773)
            ·
              refine ⟨1105040796959142278339915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2946775458557712742239773 1105040796959142278339915)
              ·
                refine ⟨1657561195438713417509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105040796959142278339915 1657561195438713417509873)
                ·
                  refine ⟨1243170896579035063132405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1657561195438713417509873 1243170896579035063132405)
                  ·
                    refine ⟨116547271554284537168663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1243170896579035063132405 116547271554284537168663)
                    ·
                      rfl

theorem cell23_680925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_680925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680925 prefixEnd_680925 := by exact prefixLift 680925
  have htrace : WordTrace (prefixWord ++ tailWord_680925) baseStart_680925 baseEnd_680925 := by
    simpa [prefixWord, tailWord_680925, baseEnd_680925] using wordTrace_append hprefix tailTrace_680925
  have hstable : (prefixWord ++ tailWord_680925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680925).length < 2 ^ (prefixWord ++ tailWord_680925).sum := by decide
  have hdescent : baseEnd_680925 < baseStart_680925 := by decide
  rcases family_descends (prefixWord ++ tailWord_680925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680945 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_680945 : Nat := 118140960795 + 680945 * 2 ^ 59
def prefixEnd_680945 : Nat := 4983230072969 + 3 ^ 40 * 680945 * 2
def baseEnd_680945 : Nat := 349652084275943533255897

theorem tailTrace_680945 : CollatzResearch.WordTrace tailWord_680945 prefixEnd_680945 349652084275943533255897 := by
  unfold tailWord_680945
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836104518060035992300289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16557403012040023994866859 24836104518060035992300289)
  ·
    refine ⟨18627078388545026994225217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24836104518060035992300289 18627078388545026994225217)
    ·
      refine ⟨13970308791408770245668913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18627078388545026994225217 13970308791408770245668913)
      ·
        refine ⟨10477731593556577684251685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13970308791408770245668913 10477731593556577684251685)
        ·
          refine ⟨1964574673791858315797191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10477731593556577684251685 1964574673791858315797191)
          ·
            refine ⟨2946862010687787473695787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964574673791858315797191 2946862010687787473695787)
            ·
              refine ⟨4420293016031681210543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946862010687787473695787 4420293016031681210543681)
              ·
                refine ⟨3315219762023760907907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4420293016031681210543681 3315219762023760907907761)
                ·
                  refine ⟨2486414821517820680930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3315219762023760907907761 2486414821517820680930821)
                  ·
                    refine ⟨466202779034591377674529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2486414821517820680930821 466202779034591377674529)
                    ·
                      refine ⟨349652084275943533255897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 466202779034591377674529 349652084275943533255897)
                      ·
                        rfl

theorem cell23_680945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_680945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_680945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_680945 prefixEnd_680945 := by exact prefixLift 680945
  have htrace : WordTrace (prefixWord ++ tailWord_680945) baseStart_680945 baseEnd_680945 := by
    simpa [prefixWord, tailWord_680945, baseEnd_680945] using wordTrace_append hprefix tailTrace_680945
  have hstable : (prefixWord ++ tailWord_680945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680945).length < 2 ^ (prefixWord ++ tailWord_680945).sum := by decide
  have hdescent : baseEnd_680945 < baseStart_680945 := by decide
  rcases family_descends (prefixWord ++ tailWord_680945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681001 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_681001 : Nat := 118140960795 + 681001 * 2 ^ 59
def prefixEnd_681001 : Nat := 4983230072969 + 3 ^ 40 * 681001 * 2
def baseEnd_681001 : Nat := 349680839192595314155639

theorem tailTrace_681001 : CollatzResearch.WordTrace tailWord_681001 prefixEnd_681001 349680839192595314155639 := by
  unfold tailWord_681001
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838147005857157556338857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16558764670571438370892571 24838147005857157556338857)
  ·
    refine ⟨18628610254392868167254143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24838147005857157556338857 18628610254392868167254143)
    ·
      refine ⟨27942915381589302250881215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18628610254392868167254143 27942915381589302250881215)
      ·
        refine ⟨41914373072383953376321823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27942915381589302250881215 41914373072383953376321823)
        ·
          refine ⟨62871559608575930064482735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41914373072383953376321823 62871559608575930064482735)
          ·
            refine ⟨94307339412863895096724103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62871559608575930064482735 94307339412863895096724103)
            ·
              refine ⟨141461009119295842645086155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94307339412863895096724103 141461009119295842645086155)
              ·
                refine ⟨212191513678943763967629233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141461009119295842645086155 212191513678943763967629233)
                ·
                  refine ⟨159143635259207822975721925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212191513678943763967629233 159143635259207822975721925)
                  ·
                    refine ⟨29839431611101466807947861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159143635259207822975721925 29839431611101466807947861)
                    ·
                      refine ⟨349680839192595314155639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 29839431611101466807947861 349680839192595314155639)
                      ·
                        rfl

theorem cell23_681001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_681001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681001 prefixEnd_681001 := by exact prefixLift 681001
  have htrace : WordTrace (prefixWord ++ tailWord_681001) baseStart_681001 baseEnd_681001 := by
    simpa [prefixWord, tailWord_681001, baseEnd_681001] using wordTrace_append hprefix tailTrace_681001
  have hstable : (prefixWord ++ tailWord_681001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681001).length < 2 ^ (prefixWord ++ tailWord_681001).sum := by decide
  have hdescent : baseEnd_681001 < baseStart_681001 := by decide
  rcases family_descends (prefixWord ++ tailWord_681001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681102 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_681102 : Nat := 118140960795 + 681102 * 2 ^ 59
def prefixEnd_681102 : Nat := 4983230072969 + 3 ^ 40 * 681102 * 2
def baseEnd_681102 : Nat := 349732700738699418992675

theorem tailTrace_681102 : CollatzResearch.WordTrace tailWord_681102 prefixEnd_681102 349732700738699418992675 := by
  unfold tailWord_681102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105228847311406475720695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16561220518994167870510373 3105228847311406475720695)
  ·
    refine ⟨4657843270967109713581043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3105228847311406475720695 4657843270967109713581043)
    ·
      refine ⟨6986764906450664570371565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657843270967109713581043 6986764906450664570371565)
      ·
        refine ⟨2620036839918999213889337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6986764906450664570371565 2620036839918999213889337)
        ·
          refine ⟨1965027629939249410417003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2620036839918999213889337 1965027629939249410417003)
          ·
            refine ⟨2947541444908874115625505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965027629939249410417003 2947541444908874115625505)
            ·
              refine ⟨2210656083681655586719129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947541444908874115625505 2210656083681655586719129)
              ·
                refine ⟨1657992062761241690039347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210656083681655586719129 1657992062761241690039347)
                ·
                  refine ⟨2486988094141862535059021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657992062761241690039347 2486988094141862535059021)
                  ·
                    refine ⟨932620535303198450647133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2486988094141862535059021 932620535303198450647133)
                    ·
                      refine ⟨349732700738699418992675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932620535303198450647133 349732700738699418992675)
                      ·
                        rfl

theorem cell23_681102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_681102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681102 prefixEnd_681102 := by exact prefixLift 681102
  have htrace : WordTrace (prefixWord ++ tailWord_681102) baseStart_681102 baseEnd_681102 := by
    simpa [prefixWord, tailWord_681102, baseEnd_681102] using wordTrace_append hprefix tailTrace_681102
  have hstable : (prefixWord ++ tailWord_681102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681102).length < 2 ^ (prefixWord ++ tailWord_681102).sum := by decide
  have hdescent : baseEnd_681102 < baseStart_681102 := by decide
  rcases family_descends (prefixWord ++ tailWord_681102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681106 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_681106 : Nat := 118140960795 + 681106 * 2 ^ 59
def prefixEnd_681106 : Nat := 4983230072969 + 3 ^ 40 * 681106 * 2
def baseEnd_681106 : Nat := 349734754661317403342657

theorem tailTrace_681106 : CollatzResearch.WordTrace tailWord_681106 prefixEnd_681106 349734754661317403342657 := by
  unfold tailWord_681106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210494167619190122227793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16561317780317840325940781 6210494167619190122227793)
  ·
    refine ⟨4657870625714392591670845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6210494167619190122227793 4657870625714392591670845)
    ·
      refine ⟨1746701484642897221876567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4657870625714392591670845 1746701484642897221876567)
      ·
        refine ⟨2620052226964345832814851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746701484642897221876567 2620052226964345832814851)
        ·
          refine ⟨3930078340446518749222277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620052226964345832814851 3930078340446518749222277)
          ·
            refine ⟨736889688833722265479177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3930078340446518749222277 736889688833722265479177)
            ·
              refine ⟨552667266625291699109383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736889688833722265479177 552667266625291699109383)
              ·
                refine ⟨829000899937937548664075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552667266625291699109383 829000899937937548664075)
                ·
                  refine ⟨1243501349906906322996113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829000899937937548664075 1243501349906906322996113)
                  ·
                    refine ⟨932626012430179742247085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1243501349906906322996113 932626012430179742247085)
                    ·
                      refine ⟨349734754661317403342657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932626012430179742247085 349734754661317403342657)
                      ·
                        rfl

theorem cell23_681106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_681106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681106 prefixEnd_681106 := by exact prefixLift 681106
  have htrace : WordTrace (prefixWord ++ tailWord_681106) baseStart_681106 baseEnd_681106 := by
    simpa [prefixWord, tailWord_681106, baseEnd_681106] using wordTrace_append hprefix tailTrace_681106
  have hstable : (prefixWord ++ tailWord_681106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681106).length < 2 ^ (prefixWord ++ tailWord_681106).sum := by decide
  have hdescent : baseEnd_681106 < baseStart_681106 := by decide
  rcases family_descends (prefixWord ++ tailWord_681106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681119 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 3]
def baseStart_681119 : Nat := 118140960795 + 681119 * 2 ^ 59
def prefixEnd_681119 : Nat := 4983230072969 + 3 ^ 40 * 681119 * 2
def baseEnd_681119 : Nat := 349741429909825852480097

theorem tailTrace_681119 : CollatzResearch.WordTrace tailWord_681119 prefixEnd_681119 349741429909825852480097 := by
  unfold tailWord_681119
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842450819429663709134411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16561633879619775806089607 24842450819429663709134411)
  ·
    refine ⟨37263676229144495563701617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24842450819429663709134411 37263676229144495563701617)
    ·
      refine ⟨27947757171858371672776213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37263676229144495563701617 27947757171858371672776213)
      ·
        refine ⟨1310051117430861172161385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27947757171858371672776213 1310051117430861172161385)
        ·
          refine ⟨982538338073145879121039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310051117430861172161385 982538338073145879121039)
          ·
            refine ⟨1473807507109718818681559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982538338073145879121039 1473807507109718818681559)
            ·
              refine ⟨2210711260664578228022339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473807507109718818681559 2210711260664578228022339)
              ·
                refine ⟨3316066890996867342033509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210711260664578228022339 3316066890996867342033509)
                ·
                  refine ⟨621762542061912626631283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3316066890996867342033509 621762542061912626631283)
                  ·
                    refine ⟨932643813092868939946925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621762542061912626631283 932643813092868939946925)
                    ·
                      refine ⟨349741429909825852480097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932643813092868939946925 349741429909825852480097)
                      ·
                        rfl

theorem cell23_681119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_681119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681119 prefixEnd_681119 := by exact prefixLift 681119
  have htrace : WordTrace (prefixWord ++ tailWord_681119) baseStart_681119 baseEnd_681119 := by
    simpa [prefixWord, tailWord_681119, baseEnd_681119] using wordTrace_append hprefix tailTrace_681119
  have hstable : (prefixWord ++ tailWord_681119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681119).length < 2 ^ (prefixWord ++ tailWord_681119).sum := by decide
  have hdescent : baseEnd_681119 < baseStart_681119 := by decide
  rcases family_descends (prefixWord ++ tailWord_681119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681154 : List Nat := [3, 5, 1, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_681154 : Nat := 118140960795 + 681154 * 2 ^ 59
def prefixEnd_681154 : Nat := 4983230072969 + 3 ^ 40 * 681154 * 2
def baseEnd_681154 : Nat := 349759401732733215542437

theorem tailTrace_681154 : CollatzResearch.WordTrace tailWord_681154 prefixEnd_681154 349759401732733215542437 := by
  unfold tailWord_681154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210931843575716171664629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16562484916201909791105677 6210931843575716171664629)
  ·
    refine ⟨582274860335223391093559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6210931843575716171664629 582274860335223391093559)
    ·
      refine ⟨873412290502835086640339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582274860335223391093559 873412290502835086640339)
      ·
        refine ⟨1310118435754252629960509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873412290502835086640339 1310118435754252629960509)
        ·
          refine ⟨491294413407844736235191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1310118435754252629960509 491294413407844736235191)
          ·
            refine ⟨736941620111767104352787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491294413407844736235191 736941620111767104352787)
            ·
              refine ⟨1105412430167650656529181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736941620111767104352787 1105412430167650656529181)
              ·
                refine ⟨414529661312868996198443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105412430167650656529181 414529661312868996198443)
                ·
                  refine ⟨621794491969303494297665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414529661312868996198443 621794491969303494297665)
                  ·
                    refine ⟨466345868976977620723249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 621794491969303494297665 466345868976977620723249)
                    ·
                      refine ⟨349759401732733215542437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 466345868976977620723249 349759401732733215542437)
                      ·
                        rfl

theorem cell23_681154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_681154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681154 prefixEnd_681154 := by exact prefixLift 681154
  have htrace : WordTrace (prefixWord ++ tailWord_681154) baseStart_681154 baseEnd_681154 := by
    simpa [prefixWord, tailWord_681154, baseEnd_681154] using wordTrace_append hprefix tailTrace_681154
  have hstable : (prefixWord ++ tailWord_681154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681154).length < 2 ^ (prefixWord ++ tailWord_681154).sum := by decide
  have hdescent : baseEnd_681154 < baseStart_681154 := by decide
  rcases family_descends (prefixWord ++ tailWord_681154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681168 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_681168 : Nat := 118140960795 + 681168 * 2 ^ 59
def prefixEnd_681168 : Nat := 4983230072969 + 3 ^ 40 * 681168 * 2
def baseEnd_681168 : Nat := 349766590461896160767371

theorem tailTrace_681168 : CollatzResearch.WordTrace tailWord_681168 prefixEnd_681168 349766590461896160767371 := by
  unfold tailWord_681168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422118998126072538834079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16562825330834763385112105 12422118998126072538834079)
  ·
    refine ⟨18633178497189108808251119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12422118998126072538834079 18633178497189108808251119)
    ·
      refine ⟨27949767745783663212376679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18633178497189108808251119 27949767745783663212376679)
      ·
        refine ⟨41924651618675494818565019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27949767745783663212376679 41924651618675494818565019)
        ·
          refine ⟨62886977428013242227847529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41924651618675494818565019 62886977428013242227847529)
          ·
            refine ⟨47165233071009931670885647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62886977428013242227847529 47165233071009931670885647)
            ·
              refine ⟨70747849606514897506328471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47165233071009931670885647 70747849606514897506328471)
              ·
                refine ⟨106121774409772346259492707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70747849606514897506328471 106121774409772346259492707)
                ·
                  refine ⟨159182661614658519389239061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106121774409772346259492707 159182661614658519389239061)
                  ·
                    refine ⟨7461687263187118096370581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159182661614658519389239061 7461687263187118096370581)
                    ·
                      refine ⟨349766590461896160767371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7461687263187118096370581 349766590461896160767371)
                      ·
                        rfl

theorem cell23_681168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_681168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681168 prefixEnd_681168 := by exact prefixLift 681168
  have htrace : WordTrace (prefixWord ++ tailWord_681168) baseStart_681168 baseEnd_681168 := by
    simpa [prefixWord, tailWord_681168, baseEnd_681168] using wordTrace_append hprefix tailTrace_681168
  have hstable : (prefixWord ++ tailWord_681168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681168).length < 2 ^ (prefixWord ++ tailWord_681168).sum := by decide
  have hdescent : baseEnd_681168 < baseStart_681168 := by decide
  rcases family_descends (prefixWord ++ tailWord_681168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681175 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_681175 : Nat := 118140960795 + 681175 * 2 ^ 59
def prefixEnd_681175 : Nat := 4983230072969 + 3 ^ 40 * 681175 * 2
def baseEnd_681175 : Nat := 349770184826477633379839

theorem tailTrace_681175 : CollatzResearch.WordTrace tailWord_681175 prefixEnd_681175 349770184826477633379839 := by
  unfold tailWord_681175
  simp only [CollatzResearch.WordTrace]
  refine ⟨24844493307226785273172979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16562995538151190182115319 24844493307226785273172979)
  ·
    refine ⟨37266739960840177909759469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24844493307226785273172979 37266739960840177909759469)
    ·
      refine ⟨13975027485315066716159801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37266739960840177909759469 13975027485315066716159801)
      ·
        refine ⟨10481270613986300037119851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13975027485315066716159801 10481270613986300037119851)
        ·
          refine ⟨15721905920979450055679777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10481270613986300037119851 15721905920979450055679777)
          ·
            refine ⟨11791429440734587541759833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15721905920979450055679777 11791429440734587541759833)
            ·
              refine ⟨8843572080550940656319875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11791429440734587541759833 8843572080550940656319875)
              ·
                refine ⟨13265358120826410984479813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8843572080550940656319875 13265358120826410984479813)
                ·
                  refine ⟨2487254647654952059589965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13265358120826410984479813 2487254647654952059589965)
                  ·
                    refine ⟨932720492870607022346237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2487254647654952059589965 932720492870607022346237)
                    ·
                      refine ⟨349770184826477633379839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932720492870607022346237 349770184826477633379839)
                      ·
                        rfl

theorem cell23_681175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_681175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681175 prefixEnd_681175 := by exact prefixLift 681175
  have htrace : WordTrace (prefixWord ++ tailWord_681175) baseStart_681175 baseEnd_681175 := by
    simpa [prefixWord, tailWord_681175, baseEnd_681175] using wordTrace_append hprefix tailTrace_681175
  have hstable : (prefixWord ++ tailWord_681175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681175).length < 2 ^ (prefixWord ++ tailWord_681175).sum := by decide
  have hdescent : baseEnd_681175 < baseStart_681175 := by decide
  rcases family_descends (prefixWord ++ tailWord_681175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681235 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3]
def baseStart_681235 : Nat := 118140960795 + 681235 * 2 ^ 59
def prefixEnd_681235 : Nat := 4983230072969 + 3 ^ 40 * 681235 * 2
def baseEnd_681235 : Nat := 349800993665747398629563

theorem tailTrace_681235 : CollatzResearch.WordTrace tailWord_681235 prefixEnd_681235 349800993665747398629563 := by
  unfold tailWord_681235
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846681687009415520357159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16564454458006277013571439 24846681687009415520357159)
  ·
    refine ⟨37270022530514123280535739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24846681687009415520357159 37270022530514123280535739)
    ·
      refine ⟨55905033795771184920803609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37270022530514123280535739 55905033795771184920803609)
      ·
        refine ⟨41928775346828388690602707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55905033795771184920803609 41928775346828388690602707)
        ·
          refine ⟨62893163020242583035904061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41928775346828388690602707 62893163020242583035904061)
          ·
            refine ⟨23584936132590968638464023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62893163020242583035904061 23584936132590968638464023)
            ·
              refine ⟨35377404198886452957696035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23584936132590968638464023 35377404198886452957696035)
              ·
                refine ⟨53066106298329679436544053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35377404198886452957696035 53066106298329679436544053)
                ·
                  refine ⟨4974947465468407447176005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53066106298329679436544053 4974947465468407447176005)
                  ·
                    refine ⟨932802649775326396345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974947465468407447176005 932802649775326396345501)
                    ·
                      refine ⟨349800993665747398629563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932802649775326396345501 349800993665747398629563)
                      ·
                        rfl

theorem cell23_681235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_681235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681235 prefixEnd_681235 := by exact prefixLift 681235
  have htrace : WordTrace (prefixWord ++ tailWord_681235) baseStart_681235 baseEnd_681235 := by
    simpa [prefixWord, tailWord_681235, baseEnd_681235] using wordTrace_append hprefix tailTrace_681235
  have hstable : (prefixWord ++ tailWord_681235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681235).length < 2 ^ (prefixWord ++ tailWord_681235).sum := by decide
  have hdescent : baseEnd_681235 < baseStart_681235 := by decide
  rcases family_descends (prefixWord ++ tailWord_681235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681252 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_681252 : Nat := 118140960795 + 681252 * 2 ^ 59
def prefixEnd_681252 : Nat := 4983230072969 + 3 ^ 40 * 681252 * 2
def baseEnd_681252 : Nat := 349809722836873832116985

theorem tailTrace_681252 : CollatzResearch.WordTrace tailWord_681252 prefixEnd_681252 349809722836873832116985 := by
  unfold tailWord_681252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12423650863973913711863005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16564867818631884949150673 12423650863973913711863005)
  ·
    refine ⟨4658869073990217641948627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12423650863973913711863005 4658869073990217641948627)
    ·
      refine ⟨6988303610985326462922941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4658869073990217641948627 6988303610985326462922941)
      ·
        refine ⟨2620613854119497423596103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6988303610985326462922941 2620613854119497423596103)
        ·
          refine ⟨3930920781179246135394155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620613854119497423596103 3930920781179246135394155)
          ·
            refine ⟨5896381171768869203091233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930920781179246135394155 5896381171768869203091233)
            ·
              refine ⟨4422285878826651902318425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5896381171768869203091233 4422285878826651902318425)
              ·
                refine ⟨3316714409119988926738819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422285878826651902318425 3316714409119988926738819)
                ·
                  refine ⟨4975071613679983390108229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316714409119988926738819 4975071613679983390108229)
                  ·
                    refine ⟨932825927564996885645293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975071613679983390108229 932825927564996885645293)
                    ·
                      refine ⟨349809722836873832116985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932825927564996885645293 349809722836873832116985)
                      ·
                        rfl

theorem cell23_681252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_681252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681252 prefixEnd_681252 := by exact prefixLift 681252
  have htrace : WordTrace (prefixWord ++ tailWord_681252) baseStart_681252 baseEnd_681252 := by
    simpa [prefixWord, tailWord_681252, baseEnd_681252] using wordTrace_append hprefix tailTrace_681252
  have hstable : (prefixWord ++ tailWord_681252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681252).length < 2 ^ (prefixWord ++ tailWord_681252).sum := by decide
  have hdescent : baseEnd_681252 < baseStart_681252 := by decide
  rcases family_descends (prefixWord ++ tailWord_681252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681269 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_681269 : Nat := 118140960795 + 681269 * 2 ^ 59
def prefixEnd_681269 : Nat := 4983230072969 + 3 ^ 40 * 681269 * 2
def baseEnd_681269 : Nat := 349818452008000265604407

theorem tailTrace_681269 : CollatzResearch.WordTrace tailWord_681269 prefixEnd_681269 349818452008000265604407 := by
  unfold tailWord_681269
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847921768886239327094861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16565281179257492884729907 24847921768886239327094861)
  ·
    refine ⟨9317970663332339747660573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24847921768886239327094861 9317970663332339747660573)
    ·
      refine ⟨3494238998749627405372715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9317970663332339747660573 3494238998749627405372715)
      ·
        refine ⟨5241358498124441108059073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494238998749627405372715 5241358498124441108059073)
        ·
          refine ⟨3931018873593330831044305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5241358498124441108059073 3931018873593330831044305)
          ·
            refine ⟨2948264155194998123283229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3931018873593330831044305 2948264155194998123283229)
            ·
              refine ⟨1105599058198124296231211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2948264155194998123283229 1105599058198124296231211)
              ·
                refine ⟨1658398587297186444346817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105599058198124296231211 1658398587297186444346817)
                ·
                  refine ⟨1243798940472889833260113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1658398587297186444346817 1243798940472889833260113)
                  ·
                    refine ⟨932849205354667374945085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1243798940472889833260113 932849205354667374945085)
                    ·
                      refine ⟨349818452008000265604407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932849205354667374945085 349818452008000265604407)
                      ·
                        rfl

theorem cell23_681269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_681269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681269 prefixEnd_681269 := by exact prefixLift 681269
  have htrace : WordTrace (prefixWord ++ tailWord_681269) baseStart_681269 baseEnd_681269 := by
    simpa [prefixWord, tailWord_681269, baseEnd_681269] using wordTrace_append hprefix tailTrace_681269
  have hstable : (prefixWord ++ tailWord_681269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681269).length < 2 ^ (prefixWord ++ tailWord_681269).sum := by decide
  have hdescent : baseEnd_681269 < baseStart_681269 := by decide
  rcases family_descends (prefixWord ++ tailWord_681269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681276 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_681276 : Nat := 118140960795 + 681276 * 2 ^ 59
def prefixEnd_681276 : Nat := 4983230072969 + 3 ^ 40 * 681276 * 2
def baseEnd_681276 : Nat := 116607348790860579405625

theorem tailTrace_681276 : CollatzResearch.WordTrace tailWord_681276 prefixEnd_681276 116607348790860579405625 := by
  unfold tailWord_681276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424088539930439761299841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16565451386573919681733121 12424088539930439761299841)
  ·
    refine ⟨9318066404947829820974881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12424088539930439761299841 9318066404947829820974881)
    ·
      refine ⟨6988549803710872365731161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9318066404947829820974881 6988549803710872365731161)
      ·
        refine ⟨5241412352783154274298371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6988549803710872365731161 5241412352783154274298371)
        ·
          refine ⟨7862118529174731411447557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241412352783154274298371 7862118529174731411447557)
          ·
            refine ⟨1474147224220262139646417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7862118529174731411447557 1474147224220262139646417)
            ·
              refine ⟨1105610418165196604734813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474147224220262139646417 1105610418165196604734813)
              ·
                refine ⟨414603906811948726775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105610418165196604734813 414603906811948726775555)
                ·
                  refine ⟨621905860217923090163333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414603906811948726775555 621905860217923090163333)
                  ·
                    refine ⟨116607348790860579405625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621905860217923090163333 116607348790860579405625)
                    ·
                      rfl

theorem cell23_681276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_681276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681276 prefixEnd_681276 := by exact prefixLift 681276
  have htrace : WordTrace (prefixWord ++ tailWord_681276) baseStart_681276 baseEnd_681276 := by
    simpa [prefixWord, tailWord_681276, baseEnd_681276] using wordTrace_append hprefix tailTrace_681276
  have hstable : (prefixWord ++ tailWord_681276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681276).length < 2 ^ (prefixWord ++ tailWord_681276).sum := by decide
  have hdescent : baseEnd_681276 < baseStart_681276 := by decide
  rcases family_descends (prefixWord ++ tailWord_681276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681293 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_681293 : Nat := 118140960795 + 681293 * 2 ^ 59
def prefixEnd_681293 : Nat := 4983230072969 + 3 ^ 40 * 681293 * 2
def baseEnd_681293 : Nat := 116610258514569390568099

theorem tailTrace_681293 : CollatzResearch.WordTrace tailWord_681293 prefixEnd_681293 116610258514569390568099 := by
  unfold tailWord_681293
  simp only [CollatzResearch.WordTrace]
  refine ⟨24848797120799291425968533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16565864747199527617312355 24848797120799291425968533)
  ·
    refine ⟨1164787365037466785592275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24848797120799291425968533 1164787365037466785592275)
    ·
      refine ⟨1747181047556200178388413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164787365037466785592275 1747181047556200178388413)
      ·
        refine ⟨655192892833575066895655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1747181047556200178388413 655192892833575066895655)
        ·
          refine ⟨982789339250362600343483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655192892833575066895655 982789339250362600343483)
          ·
            refine ⟨1474184008875543900515225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982789339250362600343483 1474184008875543900515225)
            ·
              refine ⟨1105638006656657925386419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474184008875543900515225 1105638006656657925386419)
              ·
                refine ⟨1658457009984986888079629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105638006656657925386419 1658457009984986888079629)
                ·
                  refine ⟨621921378744370083029861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1658457009984986888079629 621921378744370083029861)
                  ·
                    refine ⟨116610258514569390568099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621921378744370083029861 116610258514569390568099)
                    ·
                      rfl

theorem cell23_681293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_681293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681293 prefixEnd_681293 := by exact prefixLift 681293
  have htrace : WordTrace (prefixWord ++ tailWord_681293) baseStart_681293 baseEnd_681293 := by
    simpa [prefixWord, tailWord_681293, baseEnd_681293] using wordTrace_append hprefix tailTrace_681293
  have hstable : (prefixWord ++ tailWord_681293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681293).length < 2 ^ (prefixWord ++ tailWord_681293).sum := by decide
  have hdescent : baseEnd_681293 < baseStart_681293 := by decide
  rcases family_descends (prefixWord ++ tailWord_681293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681299 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 3]
def baseStart_681299 : Nat := 118140960795 + 681299 * 2 ^ 59
def prefixEnd_681299 : Nat := 4983230072969 + 3 ^ 40 * 681299 * 2
def baseEnd_681299 : Nat := 349833856427635148229269

theorem tailTrace_681299 : CollatzResearch.WordTrace tailWord_681299 prefixEnd_681299 349833856427635148229269 := by
  unfold tailWord_681299
  simp only [CollatzResearch.WordTrace]
  refine ⟨24849015958777554450686951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16566010639185036300457967 24849015958777554450686951)
  ·
    refine ⟨37273523938166331676030427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24849015958777554450686951 37273523938166331676030427)
    ·
      refine ⟨55910285907249497514045641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37273523938166331676030427 55910285907249497514045641)
      ·
        refine ⟨41932714430437123135534231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55910285907249497514045641 41932714430437123135534231)
        ·
          refine ⟨62899071645655684703301347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41932714430437123135534231 62899071645655684703301347)
          ·
            refine ⟨94348607468483527054952021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62899071645655684703301347 94348607468483527054952021)
            ·
              refine ⟨1105647743771291332675219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 94348607468483527054952021 1105647743771291332675219)
              ·
                refine ⟨1658471615656936999012829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105647743771291332675219 1658471615656936999012829)
                ·
                  refine ⟨621926855871351374629811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1658471615656936999012829 621926855871351374629811)
                  ·
                    refine ⟨932890283807027061944717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621926855871351374629811 932890283807027061944717)
                    ·
                      refine ⟨349833856427635148229269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 932890283807027061944717 349833856427635148229269)
                      ·
                        rfl

theorem cell23_681299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_681299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681299 prefixEnd_681299 := by exact prefixLift 681299
  have htrace : WordTrace (prefixWord ++ tailWord_681299) baseStart_681299 baseEnd_681299 := by
    simpa [prefixWord, tailWord_681299, baseEnd_681299] using wordTrace_append hprefix tailTrace_681299
  have hstable : (prefixWord ++ tailWord_681299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681299).length < 2 ^ (prefixWord ++ tailWord_681299).sum := by decide
  have hdescent : baseEnd_681299 < baseStart_681299 := by decide
  rcases family_descends (prefixWord ++ tailWord_681299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681352 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_681352 : Nat := 118140960795 + 681352 * 2 ^ 59
def prefixEnd_681352 : Nat := 4983230072969 + 3 ^ 40 * 681352 * 2
def baseEnd_681352 : Nat := 349861070902323440866525

theorem tailTrace_681352 : CollatzResearch.WordTrace tailWord_681352 prefixEnd_681352 349861070902323440866525 := by
  unfold tailWord_681352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12425474513792772251183155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16567299351723696334910873 12425474513792772251183155)
  ·
    refine ⟨18638211770689158376774733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12425474513792772251183155 18638211770689158376774733)
    ·
      refine ⟨6989329414008434391290525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18638211770689158376774733 6989329414008434391290525)
      ·
        refine ⟨2620998530253162896733947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6989329414008434391290525 2620998530253162896733947)
        ·
          refine ⟨3931497795379744345100921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620998530253162896733947 3931497795379744345100921)
          ·
            refine ⟨2948623346534808258825691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3931497795379744345100921 2948623346534808258825691)
            ·
              refine ⟨4422935019802212388238537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948623346534808258825691 4422935019802212388238537)
              ·
                refine ⟨3317201264851659291178903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422935019802212388238537 3317201264851659291178903)
                ·
                  refine ⟨4975801897277488936768355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317201264851659291178903 4975801897277488936768355)
                  ·
                    refine ⟨7463702845916233405152533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975801897277488936768355 7463702845916233405152533)
                    ·
                      refine ⟨349861070902323440866525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7463702845916233405152533 349861070902323440866525)
                      ·
                        rfl

theorem cell23_681352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_681352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681352 prefixEnd_681352 := by exact prefixLift 681352
  have htrace : WordTrace (prefixWord ++ tailWord_681352) baseStart_681352 baseEnd_681352 := by
    simpa [prefixWord, tailWord_681352, baseEnd_681352] using wordTrace_append hprefix tailTrace_681352
  have hstable : (prefixWord ++ tailWord_681352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681352).length < 2 ^ (prefixWord ++ tailWord_681352).sum := by decide
  have hdescent : baseEnd_681352 < baseStart_681352 := by decide
  rcases family_descends (prefixWord ++ tailWord_681352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681422 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_681422 : Nat := 118140960795 + 681422 * 2 ^ 59
def prefixEnd_681422 : Nat := 4983230072969 + 3 ^ 40 * 681422 * 2
def baseEnd_681422 : Nat := 116632338182712722330401

theorem tailTrace_681422 : CollatzResearch.WordTrace tailWord_681422 prefixEnd_681422 116632338182712722330401 := by
  unfold tailWord_681422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106687767166493307176815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16569001424887964304943013 3106687767166493307176815)
  ·
    refine ⟨4660031650749739960765223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3106687767166493307176815 4660031650749739960765223)
    ·
      refine ⟨6990047476124609941147835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660031650749739960765223 6990047476124609941147835)
      ·
        refine ⟨10485071214186914911721753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990047476124609941147835 10485071214186914911721753)
        ·
          refine ⟨7863803410640186183791315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10485071214186914911721753 7863803410640186183791315)
          ·
            refine ⟨11795705115960279275686973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863803410640186183791315 11795705115960279275686973)
            ·
              refine ⟨4423389418485104728382615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11795705115960279275686973 4423389418485104728382615)
              ·
                refine ⟨6635084127727657092573923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423389418485104728382615 6635084127727657092573923)
                ·
                  refine ⟨9952626191591485638860885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635084127727657092573923 9952626191591485638860885)
                  ·
                    refine ⟨116632338182712722330401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9952626191591485638860885 116632338182712722330401)
                    ·
                      rfl

theorem cell23_681422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_681422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681422 prefixEnd_681422 := by exact prefixLift 681422
  have htrace : WordTrace (prefixWord ++ tailWord_681422) baseStart_681422 baseEnd_681422 := by
    simpa [prefixWord, tailWord_681422, baseEnd_681422] using wordTrace_append hprefix tailTrace_681422
  have hstable : (prefixWord ++ tailWord_681422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681422).length < 2 ^ (prefixWord ++ tailWord_681422).sum := by decide
  have hdescent : baseEnd_681422 < baseStart_681422 := by decide
  rcases family_descends (prefixWord ++ tailWord_681422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681432 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_681432 : Nat := 118140960795 + 681432 * 2 ^ 59
def prefixEnd_681432 : Nat := 4983230072969 + 3 ^ 40 * 681432 * 2
def baseEnd_681432 : Nat := 349902149354683127866157

theorem tailTrace_681432 : CollatzResearch.WordTrace tailWord_681432 prefixEnd_681432 349902149354683127866157 := by
  unfold tailWord_681432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12426933433647859082639275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16569244578197145443519033 12426933433647859082639275)
  ·
    refine ⟨18640400150471788623958913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12426933433647859082639275 18640400150471788623958913)
    ·
      refine ⟨13980300112853841467969185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18640400150471788623958913 13980300112853841467969185)
      ·
        refine ⟨10485225084640381100976889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13980300112853841467969185 10485225084640381100976889)
        ·
          refine ⟨7863918813480285825732667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10485225084640381100976889 7863918813480285825732667)
          ·
            refine ⟨11795878220220428738599001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863918813480285825732667 11795878220220428738599001)
            ·
              refine ⟨8846908665165321553949251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11795878220220428738599001 8846908665165321553949251)
              ·
                refine ⟨13270362997747982330923877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8846908665165321553949251 13270362997747982330923877)
                ·
                  refine ⟨2488193062077746687048227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13270362997747982330923877 2488193062077746687048227)
                  ·
                    refine ⟨3732289593116620030572341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2488193062077746687048227 3732289593116620030572341)
                    ·
                      refine ⟨349902149354683127866157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3732289593116620030572341 349902149354683127866157)
                      ·
                        rfl

theorem cell23_681432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_681432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681432 prefixEnd_681432 := by exact prefixLift 681432
  have htrace : WordTrace (prefixWord ++ tailWord_681432) baseStart_681432 baseEnd_681432 := by
    simpa [prefixWord, tailWord_681432, baseEnd_681432] using wordTrace_append hprefix tailTrace_681432
  have hstable : (prefixWord ++ tailWord_681432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681432).length < 2 ^ (prefixWord ++ tailWord_681432).sum := by decide
  have hdescent : baseEnd_681432 < baseStart_681432 := by decide
  rcases family_descends (prefixWord ++ tailWord_681432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681469 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 7]
def baseStart_681469 : Nat := 118140960795 + 681469 * 2 ^ 59
def prefixEnd_681469 : Nat := 4983230072969 + 3 ^ 40 * 681469 * 2
def baseEnd_681469 : Nat := 38880127570988831455943

theorem tailTrace_681469 : CollatzResearch.WordTrace tailWord_681469 prefixEnd_681469 38880127570988831455943 := by
  unfold tailWord_681469
  simp only [CollatzResearch.WordTrace]
  refine ⟨24855216368161673484375461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16570144245441115656250307 24855216368161673484375461)
  ·
    refine ⟨4660353069030313778320399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24855216368161673484375461 4660353069030313778320399)
    ·
      refine ⟨6990529603545470667480599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660353069030313778320399 6990529603545470667480599)
      ·
        refine ⟨10485794405318206001220899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990529603545470667480599 10485794405318206001220899)
        ·
          refine ⟨15728691607977309001831349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10485794405318206001220899 15728691607977309001831349)
          ·
            refine ⟨1474564838247872718921689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15728691607977309001831349 1474564838247872718921689)
            ·
              refine ⟨1105923628685904539191267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474564838247872718921689 1105923628685904539191267)
              ·
                refine ⟨1658885443028856808786901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105923628685904539191267 1658885443028856808786901)
                ·
                  refine ⟨38880127570988831455943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1658885443028856808786901 38880127570988831455943)
                  ·
                    rfl

theorem cell23_681469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_681469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681469 prefixEnd_681469 := by exact prefixLift 681469
  have htrace : WordTrace (prefixWord ++ tailWord_681469) baseStart_681469 baseEnd_681469 := by
    simpa [prefixWord, tailWord_681469, baseEnd_681469] using wordTrace_append hprefix tailTrace_681469
  have hstable : (prefixWord ++ tailWord_681469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681469).length < 2 ^ (prefixWord ++ tailWord_681469).sum := by decide
  have hdescent : baseEnd_681469 < baseStart_681469 := by decide
  rcases family_descends (prefixWord ++ tailWord_681469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681576 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 6]
def baseStart_681576 : Nat := 118140960795 + 681576 * 2 ^ 59
def prefixEnd_681576 : Nat := 4983230072969 + 3 ^ 40 * 681576 * 2
def baseEnd_681576 : Nat := 38886232285436729385055

theorem tailTrace_681576 : CollatzResearch.WordTrace tailWord_681576 prefixEnd_681576 38886232285436729385055 := by
  unfold tailWord_681576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429559489387015379260291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16572745985849353839013721 12429559489387015379260291)
  ·
    refine ⟨18644339234080523068890437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12429559489387015379260291 18644339234080523068890437)
    ·
      refine ⟨3495813606390098075416957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18644339234080523068890437 3495813606390098075416957)
      ·
        refine ⟨1310930102396286778281359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3495813606390098075416957 1310930102396286778281359)
        ·
          refine ⟨1966395153594430167422039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310930102396286778281359 1966395153594430167422039)
          ·
            refine ⟨2949592730391645251133059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966395153594430167422039 2949592730391645251133059)
            ·
              refine ⟨4424389095587467876699589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949592730391645251133059 4424389095587467876699589)
              ·
                refine ⟨829572955422650226881173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4424389095587467876699589 829572955422650226881173)
                ·
                  refine ⟨38886232285436729385055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 829572955422650226881173 38886232285436729385055)
                  ·
                    rfl

theorem cell23_681576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_681576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681576 prefixEnd_681576 := by exact prefixLift 681576
  have htrace : WordTrace (prefixWord ++ tailWord_681576) baseStart_681576 baseEnd_681576 := by
    simpa [prefixWord, tailWord_681576, baseEnd_681576] using wordTrace_append hprefix tailTrace_681576
  have hstable : (prefixWord ++ tailWord_681576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681576).length < 2 ^ (prefixWord ++ tailWord_681576).sum := by decide
  have hdescent : baseEnd_681576 < baseStart_681576 := by decide
  rcases family_descends (prefixWord ++ tailWord_681576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681596 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_681596 : Nat := 118140960795 + 681596 * 2 ^ 59
def prefixEnd_681596 : Nat := 4983230072969 + 3 ^ 40 * 681596 * 2
def baseEnd_681596 : Nat := 349986360182020486215403

theorem tailTrace_681596 : CollatzResearch.WordTrace tailWord_681596 prefixEnd_681596 349986360182020486215403 := by
  unfold tailWord_681596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429924219350787087124321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16573232292467716116165761 12429924219350787087124321)
  ·
    refine ⟨9322443164513090315343241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12429924219350787087124321 9322443164513090315343241)
    ·
      refine ⟨6991832373384817736507431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9322443164513090315343241 6991832373384817736507431)
      ·
        refine ⟨10487748560077226604761147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6991832373384817736507431 10487748560077226604761147)
        ·
          refine ⟨15731622840115839907141721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10487748560077226604761147 15731622840115839907141721)
          ·
            refine ⟨11798717130086879930356291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15731622840115839907141721 11798717130086879930356291)
            ·
              refine ⟨17698075695130319895534437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11798717130086879930356291 17698075695130319895534437)
              ·
                refine ⟨3318389192836934980412707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17698075695130319895534437 3318389192836934980412707)
                ·
                  refine ⟨4977583789255402470619061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318389192836934980412707 4977583789255402470619061)
                  ·
                    refine ⟨466648480242693981620537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4977583789255402470619061 466648480242693981620537)
                    ·
                      refine ⟨349986360182020486215403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 466648480242693981620537 349986360182020486215403)
                      ·
                        rfl

theorem cell23_681596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_681596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681596 prefixEnd_681596 := by exact prefixLift 681596
  have htrace : WordTrace (prefixWord ++ tailWord_681596) baseStart_681596 baseEnd_681596 := by
    simpa [prefixWord, tailWord_681596, baseEnd_681596] using wordTrace_append hprefix tailTrace_681596
  have hstable : (prefixWord ++ tailWord_681596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681596).length < 2 ^ (prefixWord ++ tailWord_681596).sum := by decide
  have hdescent : baseEnd_681596 < baseStart_681596 := by decide
  rcases family_descends (prefixWord ++ tailWord_681596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681623 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 1, 5]
def baseStart_681623 : Nat := 118140960795 + 681623 * 2 ^ 59
def prefixEnd_681623 : Nat := 4983230072969 + 3 ^ 40 * 681623 * 2
def baseEnd_681623 : Nat := 116666741386563960192593

theorem tailTrace_681623 : CollatzResearch.WordTrace tailWord_681623 prefixEnd_681623 116666741386563960192593 := by
  unfold tailWord_681623
  simp only [CollatzResearch.WordTrace]
  refine ⟨24860833209603757785481523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16573888806402505190321015 24860833209603757785481523)
  ·
    refine ⟨37291249814405636678222285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24860833209603757785481523 37291249814405636678222285)
    ·
      refine ⟨13984218680402113754333357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37291249814405636678222285 13984218680402113754333357)
      ·
        refine ⟨5244082005150792657875009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13984218680402113754333357 5244082005150792657875009)
        ·
          refine ⟨3933061503863094493406257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5244082005150792657875009 3933061503863094493406257)
          ·
            refine ⟨2949796127897320870054693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3933061503863094493406257 2949796127897320870054693)
            ·
              refine ⟨553086773980747663135255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2949796127897320870054693 553086773980747663135255)
              ·
                refine ⟨829630160971121494702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553086773980747663135255 829630160971121494702883)
                ·
                  refine ⟨1244445241456682242054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829630160971121494702883 1244445241456682242054325)
                  ·
                    refine ⟨116666741386563960192593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1244445241456682242054325 116666741386563960192593)
                    ·
                      rfl

theorem cell23_681623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_681623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681623 prefixEnd_681623 := by exact prefixLift 681623
  have htrace : WordTrace (prefixWord ++ tailWord_681623) baseStart_681623 baseEnd_681623 := by
    simpa [prefixWord, tailWord_681623, baseEnd_681623] using wordTrace_append hprefix tailTrace_681623
  have hstable : (prefixWord ++ tailWord_681623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681623).length < 2 ^ (prefixWord ++ tailWord_681623).sum := by decide
  have hdescent : baseEnd_681623 < baseStart_681623 := by decide
  rcases family_descends (prefixWord ++ tailWord_681623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681660 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_681660 : Nat := 118140960795 + 681660 * 2 ^ 59
def prefixEnd_681660 : Nat := 4983230072969 + 3 ^ 40 * 681660 * 2
def baseEnd_681660 : Nat := 350019222943908235815109

theorem tailTrace_681660 : CollatzResearch.WordTrace tailWord_681660 prefixEnd_681660 350019222943908235815109 := by
  unfold tailWord_681660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12431091355234856552289217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16574788473646475403052289 12431091355234856552289217)
  ·
    refine ⟨9323318516426142414216913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12431091355234856552289217 9323318516426142414216913)
    ·
      refine ⟨6992488887319606810662685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9323318516426142414216913 6992488887319606810662685)
      ·
        refine ⟨2622183332744852553998507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6992488887319606810662685 2622183332744852553998507)
        ·
          refine ⟨3933274999117278830997761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622183332744852553998507 3933274999117278830997761)
          ·
            refine ⟨2949956249337959123248321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3933274999117278830997761 2949956249337959123248321)
            ·
              refine ⟨2212467187003469342436241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949956249337959123248321 2212467187003469342436241)
              ·
                refine ⟨1659350390252602006827181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212467187003469342436241 1659350390252602006827181)
                ·
                  refine ⟨622256396344725752560193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1659350390252602006827181 622256396344725752560193)
                  ·
                    refine ⟨466692297258544314420145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 622256396344725752560193 466692297258544314420145)
                    ·
                      refine ⟨350019222943908235815109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 466692297258544314420145 350019222943908235815109)
                      ·
                        rfl

theorem cell23_681660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_681660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681660 prefixEnd_681660 := by exact prefixLift 681660
  have htrace : WordTrace (prefixWord ++ tailWord_681660) baseStart_681660 baseEnd_681660 := by
    simpa [prefixWord, tailWord_681660, baseEnd_681660] using wordTrace_append hprefix tailTrace_681660
  have hstable : (prefixWord ++ tailWord_681660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681660).length < 2 ^ (prefixWord ++ tailWord_681660).sum := by decide
  have hdescent : baseEnd_681660 < baseStart_681660 := by decide
  rcases family_descends (prefixWord ++ tailWord_681660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681663 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_681663 : Nat := 118140960795 + 681663 * 2 ^ 59
def prefixEnd_681663 : Nat := 4983230072969 + 3 ^ 40 * 681663 * 2
def baseEnd_681663 : Nat := 350020763385871724077595

theorem tailTrace_681663 : CollatzResearch.WordTrace tailWord_681663 prefixEnd_681663 350020763385871724077595 := by
  unfold tailWord_681663
  simp only [CollatzResearch.WordTrace]
  refine ⟨24862292129458844616937643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16574861419639229744625095 24862292129458844616937643)
  ·
    refine ⟨37293438194188266925406465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24862292129458844616937643 37293438194188266925406465)
    ·
      refine ⟨27970078645641200194054849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37293438194188266925406465 27970078645641200194054849)
      ·
        refine ⟨20977558984230900145541137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27970078645641200194054849 20977558984230900145541137)
        ·
          refine ⟨15733169238173175109155853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20977558984230900145541137 15733169238173175109155853)
          ·
            refine ⟨5899938464314940665933445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15733169238173175109155853 5899938464314940665933445)
            ·
              refine ⟨1106238462059051374862521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5899938464314940665933445 1106238462059051374862521)
              ·
                refine ⟨829678846544288531146891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106238462059051374862521 829678846544288531146891)
                ·
                  refine ⟨1244518269816432796720337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829678846544288531146891 1244518269816432796720337)
                  ·
                    refine ⟨933388702362324597540253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1244518269816432796720337 933388702362324597540253)
                    ·
                      refine ⟨350020763385871724077595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 933388702362324597540253 350020763385871724077595)
                      ·
                        rfl

theorem cell23_681663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_681663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681663 prefixEnd_681663 := by exact prefixLift 681663
  have htrace : WordTrace (prefixWord ++ tailWord_681663) baseStart_681663 baseEnd_681663 := by
    simpa [prefixWord, tailWord_681663, baseEnd_681663] using wordTrace_append hprefix tailTrace_681663
  have hstable : (prefixWord ++ tailWord_681663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681663).length < 2 ^ (prefixWord ++ tailWord_681663).sum := by decide
  have hdescent : baseEnd_681663 < baseStart_681663 := by decide
  rcases family_descends (prefixWord ++ tailWord_681663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681710 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_681710 : Nat := 118140960795 + 681710 * 2 ^ 59
def prefixEnd_681710 : Nat := 4983230072969 + 3 ^ 40 * 681710 * 2
def baseEnd_681710 : Nat := 350044896976633040189879

theorem tailTrace_681710 : CollatzResearch.WordTrace tailWord_681710 prefixEnd_681710 350044896976633040189879 := by
  unfold tailWord_681710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108000795036071455487323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16576004240192381095932389 3108000795036071455487323)
  ·
    refine ⟨4662001192554107183230985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3108000795036071455487323 4662001192554107183230985)
    ·
      refine ⟨3496500894415580387423239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4662001192554107183230985 3496500894415580387423239)
      ·
        refine ⟨5244751341623370581134859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496500894415580387423239 5244751341623370581134859)
        ·
          refine ⟨7867127012435055871702289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244751341623370581134859 7867127012435055871702289)
          ·
            refine ⟨5900345259326291903776717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867127012435055871702289 5900345259326291903776717)
            ·
              refine ⟨2212629472247359463916269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5900345259326291903776717 2212629472247359463916269)
              ·
                refine ⟨829736052092759798968601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2212629472247359463916269 829736052092759798968601)
                ·
                  refine ⟨622302039069569849226451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 829736052092759798968601 622302039069569849226451)
                  ·
                    refine ⟨933453058604354773839677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 622302039069569849226451 933453058604354773839677)
                    ·
                      refine ⟨350044896976633040189879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 933453058604354773839677 350044896976633040189879)
                      ·
                        rfl

theorem cell23_681710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_681710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681710 prefixEnd_681710 := by exact prefixLift 681710
  have htrace : WordTrace (prefixWord ++ tailWord_681710) baseStart_681710 baseEnd_681710 := by
    simpa [prefixWord, tailWord_681710, baseEnd_681710] using wordTrace_append hprefix tailTrace_681710
  have hstable : (prefixWord ++ tailWord_681710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681710).length < 2 ^ (prefixWord ++ tailWord_681710).sum := by decide
  have hdescent : baseEnd_681710 < baseStart_681710 := by decide
  rcases family_descends (prefixWord ++ tailWord_681710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681734 : List Nat := [6, 2, 2, 1, 2, 10]
def baseStart_681734 : Nat := 118140960795 + 681734 * 2 ^ 59
def prefixEnd_681734 : Nat := 4983230072969 + 3 ^ 40 * 681734 * 2
def baseEnd_681734 : Nat := 1440564693466423647283

theorem tailTrace_681734 : CollatzResearch.WordTrace tailWord_681734 prefixEnd_681734 1440564693466423647283 := by
  unfold tailWord_681734
  simp only [CollatzResearch.WordTrace]
  refine ⟨777027553506300741961633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16576587808134415828514837 777027553506300741961633)
  ·
    refine ⟨582770665129725556471225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 777027553506300741961633 582770665129725556471225)
    ·
      refine ⟨437077998847294167353419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 582770665129725556471225 437077998847294167353419)
      ·
        refine ⟨655616998270941251030129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437077998847294167353419 655616998270941251030129)
        ·
          refine ⟨491712748703205938272597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655616998270941251030129 491712748703205938272597)
          ·
            refine ⟨1440564693466423647283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 491712748703205938272597 1440564693466423647283)
            ·
              rfl

theorem cell23_681734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 10].length) (baseStart_681734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681734 prefixEnd_681734 := by exact prefixLift 681734
  have htrace : WordTrace (prefixWord ++ tailWord_681734) baseStart_681734 baseEnd_681734 := by
    simpa [prefixWord, tailWord_681734, baseEnd_681734] using wordTrace_append hprefix tailTrace_681734
  have hstable : (prefixWord ++ tailWord_681734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681734).length < 2 ^ (prefixWord ++ tailWord_681734).sum := by decide
  have hdescent : baseEnd_681734 < baseStart_681734 := by decide
  rcases family_descends (prefixWord ++ tailWord_681734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681736 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_681736 : Nat := 118140960795 + 681736 * 2 ^ 59
def prefixEnd_681736 : Nat := 4983230072969 + 3 ^ 40 * 681736 * 2
def baseEnd_681736 : Nat := 350058247473649938464759

theorem tailTrace_681736 : CollatzResearch.WordTrace tailWord_681736 prefixEnd_681736 350058247473649938464759 := by
  unfold tailWord_681736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432477329097189042172531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16576636438796252056230041 12432477329097189042172531)
  ·
    refine ⟨18648715993645783563258797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12432477329097189042172531 18648715993645783563258797)
    ·
      refine ⟨6993268497617168836222049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18648715993645783563258797 6993268497617168836222049)
      ·
        refine ⟨5244951373212876627166537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6993268497617168836222049 5244951373212876627166537)
        ·
          refine ⟨3933713529909657470374903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5244951373212876627166537 3933713529909657470374903)
          ·
            refine ⟨5900570294864486205562355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933713529909657470374903 5900570294864486205562355)
            ·
              refine ⟨8850855442296729308343533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900570294864486205562355 8850855442296729308343533)
              ·
                refine ⟨3319070790861273490628825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8850855442296729308343533 3319070790861273490628825)
                ·
                  refine ⟨2489303093145955117971619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319070790861273490628825 2489303093145955117971619)
                  ·
                    refine ⟨3733954639718932676957429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489303093145955117971619 3733954639718932676957429)
                    ·
                      refine ⟨350058247473649938464759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3733954639718932676957429 350058247473649938464759)
                      ·
                        rfl

theorem cell23_681736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_681736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681736 prefixEnd_681736 := by exact prefixLift 681736
  have htrace : WordTrace (prefixWord ++ tailWord_681736) baseStart_681736 baseEnd_681736 := by
    simpa [prefixWord, tailWord_681736, baseEnd_681736] using wordTrace_append hprefix tailTrace_681736
  have hstable : (prefixWord ++ tailWord_681736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681736).length < 2 ^ (prefixWord ++ tailWord_681736).sum := by decide
  have hdescent : baseEnd_681736 < baseStart_681736 := by decide
  rcases family_descends (prefixWord ++ tailWord_681736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681756 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 7]
def baseStart_681756 : Nat := 118140960795 + 681756 * 2 ^ 59
def prefixEnd_681756 : Nat := 4983230072969 + 3 ^ 40 * 681756 * 2
def baseEnd_681756 : Nat := 38896501898526651134963

theorem tailTrace_681756 : CollatzResearch.WordTrace tailWord_681756 prefixEnd_681756 38896501898526651134963 := by
  unfold tailWord_681756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432842059060960750036561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16577122745414614333382081 12432842059060960750036561)
  ·
    refine ⟨9324631544295720562527421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12432842059060960750036561 9324631544295720562527421)
    ·
      refine ⟨3496736829110895210947783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9324631544295720562527421 3496736829110895210947783)
      ·
        refine ⟨5245105243666342816421675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496736829110895210947783 5245105243666342816421675)
        ·
          refine ⟨7867657865499514224632513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245105243666342816421675 7867657865499514224632513)
          ·
            refine ⟨5900743399124635668474385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867657865499514224632513 5900743399124635668474385)
            ·
              refine ⟨4425557549343476751355789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900743399124635668474385 4425557549343476751355789)
              ·
                refine ⟨1659584081003803781758421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4425557549343476751355789 1659584081003803781758421)
                ·
                  refine ⟨38896501898526651134963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1659584081003803781758421 38896501898526651134963)
                  ·
                    rfl

theorem cell23_681756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_681756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681756 prefixEnd_681756 := by exact prefixLift 681756
  have htrace : WordTrace (prefixWord ++ tailWord_681756) baseStart_681756 baseEnd_681756 := by
    simpa [prefixWord, tailWord_681756, baseEnd_681756] using wordTrace_append hprefix tailTrace_681756
  have hstable : (prefixWord ++ tailWord_681756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681756).length < 2 ^ (prefixWord ++ tailWord_681756).sum := by decide
  have hdescent : baseEnd_681756 < baseStart_681756 := by decide
  rcases family_descends (prefixWord ++ tailWord_681756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681790 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_681790 : Nat := 118140960795 + 681790 * 2 ^ 59
def prefixEnd_681790 : Nat := 4983230072969 + 3 ^ 40 * 681790 * 2
def baseEnd_681790 : Nat := 38898441714332525243279

theorem tailTrace_681790 : CollatzResearch.WordTrace tailWord_681790 prefixEnd_681790 38898441714332525243279 := by
  unfold tailWord_681790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108365524999843163351353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16577949466665830204540549 3108365524999843163351353)
  ·
    refine ⟨2331274143749882372513515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3108365524999843163351353 2331274143749882372513515)
    ·
      refine ⟨3496911215624823558770273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331274143749882372513515 3496911215624823558770273)
      ·
        refine ⟨2622683411718617669077705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496911215624823558770273 2622683411718617669077705)
        ·
          refine ⟨1967012558788963251808279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2622683411718617669077705 1967012558788963251808279)
          ·
            refine ⟨2950518838183444877712419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967012558788963251808279 2950518838183444877712419)
            ·
              refine ⟨4425778257275167316568629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950518838183444877712419 4425778257275167316568629)
              ·
                refine ⟨414916711619546935928309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4425778257275167316568629 414916711619546935928309)
                ·
                  refine ⟨38898441714332525243279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414916711619546935928309 38898441714332525243279)
                  ·
                    rfl

theorem cell23_681790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_681790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681790 prefixEnd_681790 := by exact prefixLift 681790
  have htrace : WordTrace (prefixWord ++ tailWord_681790) baseStart_681790 baseEnd_681790 := by
    simpa [prefixWord, tailWord_681790, baseEnd_681790] using wordTrace_append hprefix tailTrace_681790
  have hstable : (prefixWord ++ tailWord_681790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681790).length < 2 ^ (prefixWord ++ tailWord_681790).sum := by decide
  have hdescent : baseEnd_681790 < baseStart_681790 := by decide
  rcases family_descends (prefixWord ++ tailWord_681790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681843 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3]
def baseStart_681843 : Nat := 118140960795 + 681843 * 2 ^ 59
def prefixEnd_681843 : Nat := 4983230072969 + 3 ^ 40 * 681843 * 2
def baseEnd_681843 : Nat := 350113189903681019826767

theorem tailTrace_681843 : CollatzResearch.WordTrace tailWord_681843 prefixEnd_681843 350113189903681019826767 := by
  unfold tailWord_681843
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868857268806735358490183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16579238179204490238993455 24868857268806735358490183)
  ·
    refine ⟨37303285903210103037735275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24868857268806735358490183 37303285903210103037735275)
    ·
      refine ⟨55954928854815154556602913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37303285903210103037735275 55954928854815154556602913)
      ·
        refine ⟨41966196641111365917452185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55954928854815154556602913 41966196641111365917452185)
        ·
          refine ⟨31474647480833524438089139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41966196641111365917452185 31474647480833524438089139)
          ·
            refine ⟨47211971221250286657133709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31474647480833524438089139 47211971221250286657133709)
            ·
              refine ⟨17704489207968857496425141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47211971221250286657133709 17704489207968857496425141)
              ·
                refine ⟨1659795863247080390289857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17704489207968857496425141 1659795863247080390289857)
                ·
                  refine ⟨1244846897435310292717393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1659795863247080390289857 1244846897435310292717393)
                  ·
                    refine ⟨933635173076482719538045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1244846897435310292717393 933635173076482719538045)
                    ·
                      refine ⟨350113189903681019826767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 933635173076482719538045 350113189903681019826767)
                      ·
                        rfl

theorem cell23_681843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_681843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681843 prefixEnd_681843 := by exact prefixLift 681843
  have htrace : WordTrace (prefixWord ++ tailWord_681843) baseStart_681843 baseEnd_681843 := by
    simpa [prefixWord, tailWord_681843, baseEnd_681843] using wordTrace_append hprefix tailTrace_681843
  have hstable : (prefixWord ++ tailWord_681843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681843).length < 2 ^ (prefixWord ++ tailWord_681843).sum := by decide
  have hdescent : baseEnd_681843 < baseStart_681843 := by decide
  rcases family_descends (prefixWord ++ tailWord_681843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681857 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_681857 : Nat := 118140960795 + 681857 * 2 ^ 59
def prefixEnd_681857 : Nat := 4983230072969 + 3 ^ 40 * 681857 * 2
def baseEnd_681857 : Nat := 350120378632843965051703

theorem tailTrace_681857 : CollatzResearch.WordTrace tailWord_681857 prefixEnd_681857 350120378632843965051703 := by
  unfold tailWord_681857
  simp only [CollatzResearch.WordTrace]
  refine ⟨24869367890756015749499825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16579578593837343832999883 24869367890756015749499825)
  ·
    refine ⟨18652025918067011812124869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24869367890756015749499825 18652025918067011812124869)
    ·
      refine ⟨3497254859637564714773413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18652025918067011812124869 3497254859637564714773413)
      ·
        refine ⟨655735286182043384020015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3497254859637564714773413 655735286182043384020015)
        ·
          refine ⟨983602929273065076030023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655735286182043384020015 983602929273065076030023)
          ·
            refine ⟨1475404393909597614045035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983602929273065076030023 1475404393909597614045035)
            ·
              refine ⟨2213106590864396421067553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475404393909597614045035 2213106590864396421067553)
              ·
                refine ⟨1659829943148297315800665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213106590864396421067553 1659829943148297315800665)
                ·
                  refine ⟨1244872457361222986850499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1659829943148297315800665 1244872457361222986850499)
                  ·
                    refine ⟨1867308686041834480275749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1244872457361222986850499 1867308686041834480275749)
                    ·
                      refine ⟨350120378632843965051703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1867308686041834480275749 350120378632843965051703)
                      ·
                        rfl

theorem cell23_681857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_681857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681857 prefixEnd_681857 := by exact prefixLift 681857
  have htrace : WordTrace (prefixWord ++ tailWord_681857) baseStart_681857 baseEnd_681857 := by
    simpa [prefixWord, tailWord_681857, baseEnd_681857] using wordTrace_append hprefix tailTrace_681857
  have hstable : (prefixWord ++ tailWord_681857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681857).length < 2 ^ (prefixWord ++ tailWord_681857).sum := by decide
  have hdescent : baseEnd_681857 < baseStart_681857 := by decide
  rcases family_descends (prefixWord ++ tailWord_681857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681907 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 1, 1, 3]
def baseStart_681907 : Nat := 118140960795 + 681907 * 2 ^ 59
def prefixEnd_681907 : Nat := 4983230072969 + 3 ^ 40 * 681907 * 2
def baseEnd_681907 : Nat := 350146052665568769426473

theorem tailTrace_681907 : CollatzResearch.WordTrace tailWord_681907 prefixEnd_681907 350146052665568769426473 := by
  unfold tailWord_681907
  simp only [CollatzResearch.WordTrace]
  refine ⟨24871191540574874288819975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16580794360383249525879983 24871191540574874288819975)
  ·
    refine ⟨37306787310862311433229963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24871191540574874288819975 37306787310862311433229963)
    ·
      refine ⟨55960180966293467149844945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37306787310862311433229963 55960180966293467149844945)
      ·
        refine ⟨41970135724720100362383709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55960180966293467149844945 41970135724720100362383709)
        ·
          refine ⟨15738800896770037635893891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41970135724720100362383709 15738800896770037635893891)
          ·
            refine ⟨23608201345155056453840837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15738800896770037635893891 23608201345155056453840837)
            ·
              refine ⟨4426537752216573085095157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23608201345155056453840837 4426537752216573085095157)
              ·
                refine ⟨414987914270303726727671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4426537752216573085095157 414987914270303726727671)
                ·
                  refine ⟨622481871405455590091507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414987914270303726727671 622481871405455590091507)
                  ·
                    refine ⟨933722807108183385137261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 622481871405455590091507 933722807108183385137261)
                    ·
                      refine ⟨350146052665568769426473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 933722807108183385137261 350146052665568769426473)
                      ·
                        rfl

theorem cell23_681907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 1, 3].length) (baseStart_681907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681907 prefixEnd_681907 := by exact prefixLift 681907
  have htrace : WordTrace (prefixWord ++ tailWord_681907) baseStart_681907 baseEnd_681907 := by
    simpa [prefixWord, tailWord_681907, baseEnd_681907] using wordTrace_append hprefix tailTrace_681907
  have hstable : (prefixWord ++ tailWord_681907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681907).length < 2 ^ (prefixWord ++ tailWord_681907).sum := by decide
  have hdescent : baseEnd_681907 < baseStart_681907 := by decide
  rcases family_descends (prefixWord ++ tailWord_681907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681917 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_681917 : Nat := 118140960795 + 681917 * 2 ^ 59
def prefixEnd_681917 : Nat := 4983230072969 + 3 ^ 40 * 681917 * 2
def baseEnd_681917 : Nat := 350151187472113730301427

theorem tailTrace_681917 : CollatzResearch.WordTrace tailWord_681917 prefixEnd_681917 350151187472113730301427 := by
  unfold tailWord_681917
  simp only [CollatzResearch.WordTrace]
  refine ⟨24871556270538645996684005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16581037513692430664456003 24871556270538645996684005)
  ·
    refine ⟨4663416800725996124378251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24871556270538645996684005 4663416800725996124378251)
    ·
      refine ⟨6995125201088994186567377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663416800725996124378251 6995125201088994186567377)
      ·
        refine ⟨5246343900816745639925533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6995125201088994186567377 5246343900816745639925533)
        ·
          refine ⟨1967378962806279614972075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5246343900816745639925533 1967378962806279614972075)
          ·
            refine ⟨2951068444209419422458113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967378962806279614972075 2951068444209419422458113)
            ·
              refine ⟨2213301333157064566843585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951068444209419422458113 2213301333157064566843585)
              ·
                refine ⟨1659975999867798425132689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213301333157064566843585 1659975999867798425132689)
                ·
                  refine ⟨1244981999900848818849517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1659975999867798425132689 1244981999900848818849517)
                  ·
                    refine ⟨466868249962818307068569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244981999900848818849517 466868249962818307068569)
                    ·
                      refine ⟨350151187472113730301427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 466868249962818307068569 350151187472113730301427)
                      ·
                        rfl

theorem cell23_681917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_681917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681917 prefixEnd_681917 := by exact prefixLift 681917
  have htrace : WordTrace (prefixWord ++ tailWord_681917) baseStart_681917 baseEnd_681917 := by
    simpa [prefixWord, tailWord_681917, baseEnd_681917] using wordTrace_append hprefix tailTrace_681917
  have hstable : (prefixWord ++ tailWord_681917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681917).length < 2 ^ (prefixWord ++ tailWord_681917).sum := by decide
  have hdescent : baseEnd_681917 < baseStart_681917 := by decide
  rcases family_descends (prefixWord ++ tailWord_681917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681940 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_681940 : Nat := 118140960795 + 681940 * 2 ^ 59
def prefixEnd_681940 : Nat := 4983230072969 + 3 ^ 40 * 681940 * 2
def baseEnd_681940 : Nat := 116720999175722380104607

theorem tailTrace_681940 : CollatzResearch.WordTrace tailWord_681940 prefixEnd_681940 116720999175722380104607 := by
  unfold tailWord_681940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436197574727660462385637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16581596766303547283180849 12436197574727660462385637)
  ·
    refine ⟨2331787045261436336697307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12436197574727660462385637 2331787045261436336697307)
    ·
      refine ⟨3497680567892154505045961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331787045261436336697307 3497680567892154505045961)
      ·
        refine ⟨2623260425919115878784471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3497680567892154505045961 2623260425919115878784471)
        ·
          refine ⟨3934890638878673818176707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623260425919115878784471 3934890638878673818176707)
          ·
            refine ⟨5902335958318010727265061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934890638878673818176707 5902335958318010727265061)
            ·
              refine ⟨1106687992184627011362199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5902335958318010727265061 1106687992184627011362199)
              ·
                refine ⟨1660031988276940517043299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106687992184627011362199 1660031988276940517043299)
                ·
                  refine ⟨2490047982415410775564949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660031988276940517043299 2490047982415410775564949)
                  ·
                    refine ⟨116720999175722380104607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2490047982415410775564949 116720999175722380104607)
                    ·
                      rfl

theorem cell23_681940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_681940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681940 prefixEnd_681940 := by exact prefixLift 681940
  have htrace : WordTrace (prefixWord ++ tailWord_681940) baseStart_681940 baseEnd_681940 := by
    simpa [prefixWord, tailWord_681940, baseEnd_681940] using wordTrace_append hprefix tailTrace_681940
  have hstable : (prefixWord ++ tailWord_681940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681940).length < 2 ^ (prefixWord ++ tailWord_681940).sum := by decide
  have hdescent : baseEnd_681940 < baseStart_681940 := by decide
  rcases family_descends (prefixWord ++ tailWord_681940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681994 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_681994 : Nat := 118140960795 + 681994 * 2 ^ 59
def prefixEnd_681994 : Nat := 4983230072969 + 3 ^ 40 * 681994 * 2
def baseEnd_681994 : Nat := 350190725482509929038573

theorem tailTrace_681994 : CollatzResearch.WordTrace tailWord_681994 prefixEnd_681994 350190725482509929038573 := by
  unfold tailWord_681994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6218591172814922036809259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16582909794173125431491357 6218591172814922036809259)
  ·
    refine ⟨9327886759222383055213889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6218591172814922036809259 9327886759222383055213889)
    ·
      refine ⟨6995915069416787291410417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9327886759222383055213889 6995915069416787291410417)
      ·
        refine ⟨5246936302062590468557813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6995915069416787291410417 5246936302062590468557813)
        ·
          refine ⟨491900278318367856427295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5246936302062590468557813 491900278318367856427295)
          ·
            refine ⟨737850417477551784640943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491900278318367856427295 737850417477551784640943)
            ·
              refine ⟨1106775626216327676961415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737850417477551784640943 1106775626216327676961415)
              ·
                refine ⟨1660163439324491515442123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106775626216327676961415 1660163439324491515442123)
                ·
                  refine ⟨2490245158986737273163185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660163439324491515442123 2490245158986737273163185)
                  ·
                    refine ⟨1867683869240052954872389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2490245158986737273163185 1867683869240052954872389)
                    ·
                      refine ⟨350190725482509929038573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1867683869240052954872389 350190725482509929038573)
                      ·
                        rfl

theorem cell23_681994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_681994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_681994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_681994 prefixEnd_681994 := by exact prefixLift 681994
  have htrace : WordTrace (prefixWord ++ tailWord_681994) baseStart_681994 baseEnd_681994 := by
    simpa [prefixWord, tailWord_681994, baseEnd_681994] using wordTrace_append hprefix tailTrace_681994
  have hstable : (prefixWord ++ tailWord_681994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681994).length < 2 ^ (prefixWord ++ tailWord_681994).sum := by decide
  have hdescent : baseEnd_681994 < baseStart_681994 := by decide
  rcases family_descends (prefixWord ++ tailWord_681994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682003 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_682003 : Nat := 118140960795 + 682003 * 2 ^ 59
def prefixEnd_682003 : Nat := 4983230072969 + 3 ^ 40 * 682003 * 2
def baseEnd_682003 : Nat := 350195346808400393826031

theorem tailTrace_682003 : CollatzResearch.WordTrace tailWord_682003 prefixEnd_682003 350195346808400393826031 := by
  unfold tailWord_682003
  simp only [CollatzResearch.WordTrace]
  refine ⟨24874692948227082684314663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16583128632151388456209775 24874692948227082684314663)
  ·
    refine ⟨37312039422340624026471995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24874692948227082684314663 37312039422340624026471995)
    ·
      refine ⟨55968059133510936039707993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37312039422340624026471995 55968059133510936039707993)
      ·
        refine ⟨41976044350133202029780995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55968059133510936039707993 41976044350133202029780995)
        ·
          refine ⟨62964066525199803044671493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41976044350133202029780995 62964066525199803044671493)
          ·
            refine ⟨11805762473474963070875905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62964066525199803044671493 11805762473474963070875905)
            ·
              refine ⟨8854321855106222303156929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11805762473474963070875905 8854321855106222303156929)
              ·
                refine ⟨6640741391329666727367697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8854321855106222303156929 6640741391329666727367697)
                ·
                  refine ⟨4980556043497250045525773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6640741391329666727367697 4980556043497250045525773)
                  ·
                    refine ⟨1867708516311468767072165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4980556043497250045525773 1867708516311468767072165)
                    ·
                      refine ⟨350195346808400393826031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1867708516311468767072165 350195346808400393826031)
                      ·
                        rfl

theorem cell23_682003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_682003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682003 prefixEnd_682003 := by exact prefixLift 682003
  have htrace : WordTrace (prefixWord ++ tailWord_682003) baseStart_682003 baseEnd_682003 := by
    simpa [prefixWord, tailWord_682003, baseEnd_682003] using wordTrace_append hprefix tailTrace_682003
  have hstable : (prefixWord ++ tailWord_682003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682003).length < 2 ^ (prefixWord ++ tailWord_682003).sum := by decide
  have hdescent : baseEnd_682003 < baseStart_682003 := by decide
  rcases family_descends (prefixWord ++ tailWord_682003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682140 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_682140 : Nat := 118140960795 + 682140 * 2 ^ 59
def prefixEnd_682140 : Nat := 4983230072969 + 3 ^ 40 * 682140 * 2
def baseEnd_682140 : Nat := 350265693658066357812901

theorem tailTrace_682140 : CollatzResearch.WordTrace tailWord_682140 prefixEnd_682140 350265693658066357812901 := by
  unfold tailWord_682140
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439844874365377541025937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16586459832487170054701249 12439844874365377541025937)
  ·
    refine ⟨9329883655774033155769453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12439844874365377541025937 9329883655774033155769453)
    ·
      refine ⟨3498706370915262433413545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9329883655774033155769453 3498706370915262433413545)
      ·
        refine ⟨2624029778186446825060159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3498706370915262433413545 2624029778186446825060159)
        ·
          refine ⟨3936044667279670237590239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624029778186446825060159 3936044667279670237590239)
          ·
            refine ⟨5904067000919505356385359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936044667279670237590239 5904067000919505356385359)
            ·
              refine ⟨8856100501379258034578039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904067000919505356385359 8856100501379258034578039)
              ·
                refine ⟨13284150752068887051867059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8856100501379258034578039 13284150752068887051867059)
                ·
                  refine ⟨19926226128103330577800589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13284150752068887051867059 19926226128103330577800589)
                  ·
                    refine ⟨7472334798038748966675221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19926226128103330577800589 7472334798038748966675221)
                    ·
                      refine ⟨350265693658066357812901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7472334798038748966675221 350265693658066357812901)
                      ·
                        rfl

theorem cell23_682140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_682140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682140 prefixEnd_682140 := by exact prefixLift 682140
  have htrace : WordTrace (prefixWord ++ tailWord_682140) baseStart_682140 baseEnd_682140 := by
    simpa [prefixWord, tailWord_682140, baseEnd_682140] using wordTrace_append hprefix tailTrace_682140
  have hstable : (prefixWord ++ tailWord_682140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682140).length < 2 ^ (prefixWord ++ tailWord_682140).sum := by decide
  have hdescent : baseEnd_682140 < baseStart_682140 := by decide
  rcases family_descends (prefixWord ++ tailWord_682140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682160 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_682160 : Nat := 118140960795 + 682160 * 2 ^ 59
def prefixEnd_682160 : Nat := 4983230072969 + 3 ^ 40 * 682160 * 2
def baseEnd_682160 : Nat := 350275963271156279562809

theorem tailTrace_682160 : CollatzResearch.WordTrace tailWord_682160 prefixEnd_682160 350275963271156279562809 := by
  unfold tailWord_682160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440209604329149248889967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16586946139105532331853289 12440209604329149248889967)
  ·
    refine ⟨18660314406493723873334951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12440209604329149248889967 18660314406493723873334951)
    ·
      refine ⟨27990471609740585810002427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18660314406493723873334951 27990471609740585810002427)
      ·
        refine ⟨41985707414610878715003641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27990471609740585810002427 41985707414610878715003641)
        ·
          refine ⟨31489280560958159036252731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41985707414610878715003641 31489280560958159036252731)
          ·
            refine ⟨47233920841437238554379097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31489280560958159036252731 47233920841437238554379097)
            ·
              refine ⟨35425440631077928915784323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47233920841437238554379097 35425440631077928915784323)
              ·
                refine ⟨53138160946616893373676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35425440631077928915784323 53138160946616893373676485)
                ·
                  refine ⟨9963405177490667507564341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53138160946616893373676485 9963405177490667507564341)
                  ·
                    refine ⟨934069235389750078834157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9963405177490667507564341 934069235389750078834157)
                    ·
                      refine ⟨350275963271156279562809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934069235389750078834157 350275963271156279562809)
                      ·
                        rfl

theorem cell23_682160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_682160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682160 prefixEnd_682160 := by exact prefixLift 682160
  have htrace : WordTrace (prefixWord ++ tailWord_682160) baseStart_682160 baseEnd_682160 := by
    simpa [prefixWord, tailWord_682160, baseEnd_682160] using wordTrace_append hprefix tailTrace_682160
  have hstable : (prefixWord ++ tailWord_682160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682160).length < 2 ^ (prefixWord ++ tailWord_682160).sum := by decide
  have hdescent : baseEnd_682160 < baseStart_682160 := by decide
  rcases family_descends (prefixWord ++ tailWord_682160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682187 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 5, 2]
def baseStart_682187 : Nat := 118140960795 + 682187 * 2 ^ 59
def prefixEnd_682187 : Nat := 4983230072969 + 3 ^ 40 * 682187 * 2
def baseEnd_682187 : Nat := 350289827248827673925185

theorem tailTrace_682187 : CollatzResearch.WordTrace tailWord_682187 prefixEnd_682187 350289827248827673925185 := by
  unfold tailWord_682187
  simp only [CollatzResearch.WordTrace]
  refine ⟨24881403979560482109012815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16587602653040321406008543 24881403979560482109012815)
  ·
    refine ⟨37322105969340723163519223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24881403979560482109012815 37322105969340723163519223)
    ·
      refine ⟨55983158954011084745278835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37322105969340723163519223 55983158954011084745278835)
      ·
        refine ⟨83974738431016627117918253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55983158954011084745278835 83974738431016627117918253)
        ·
          refine ⟨31490526911631235169219345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83974738431016627117918253 31490526911631235169219345)
          ·
            refine ⟨23617895183723426376914509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31490526911631235169219345 23617895183723426376914509)
            ·
              refine ⟨8856710693896284891342941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23617895183723426376914509 8856710693896284891342941)
              ·
                refine ⟨3321266510211106834253603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8856710693896284891342941 3321266510211106834253603)
                ·
                  refine ⟨4981899765316660251380405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321266510211106834253603 4981899765316660251380405)
                  ·
                    refine ⟨467053102998436898566913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4981899765316660251380405 467053102998436898566913)
                    ·
                      refine ⟨350289827248827673925185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467053102998436898566913 350289827248827673925185)
                      ·
                        rfl

theorem cell23_682187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5, 2].length) (baseStart_682187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682187 prefixEnd_682187 := by exact prefixLift 682187
  have htrace : WordTrace (prefixWord ++ tailWord_682187) baseStart_682187 baseEnd_682187 := by
    simpa [prefixWord, tailWord_682187, baseEnd_682187] using wordTrace_append hprefix tailTrace_682187
  have hstable : (prefixWord ++ tailWord_682187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682187).length < 2 ^ (prefixWord ++ tailWord_682187).sum := by decide
  have hdescent : baseEnd_682187 < baseStart_682187 := by decide
  rcases family_descends (prefixWord ++ tailWord_682187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682234 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_682234 : Nat := 118140960795 + 682234 * 2 ^ 59
def prefixEnd_682234 : Nat := 4983230072969 + 3 ^ 40 * 682234 * 2
def baseEnd_682234 : Nat := 350313960839588990037469

theorem tailTrace_682234 : CollatzResearch.WordTrace tailWord_682234 prefixEnd_682234 350313960839588990037469 := by
  unfold tailWord_682234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220779552597552283993439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16588745473593472757315837 6220779552597552283993439)
  ·
    refine ⟨9331169328896328425990159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6220779552597552283993439 9331169328896328425990159)
    ·
      refine ⟨13996753993344492638985239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9331169328896328425990159 13996753993344492638985239)
      ·
        refine ⟨20995130990016738958477859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13996753993344492638985239 20995130990016738958477859)
        ·
          refine ⟨31492696485025108437716789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20995130990016738958477859 31492696485025108437716789)
          ·
            refine ⟨2952440295471103916035949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31492696485025108437716789 2952440295471103916035949)
            ·
              refine ⟨1107165110801663968513481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2952440295471103916035949 1107165110801663968513481)
              ·
                refine ⟨830373833101247976385111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107165110801663968513481 830373833101247976385111)
                ·
                  refine ⟨1245560749651871964577667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830373833101247976385111 1245560749651871964577667)
                  ·
                    refine ⟨1868341124477807946866501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1245560749651871964577667 1868341124477807946866501)
                    ·
                      refine ⟨350313960839588990037469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1868341124477807946866501 350313960839588990037469)
                      ·
                        rfl

theorem cell23_682234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_682234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682234 prefixEnd_682234 := by exact prefixLift 682234
  have htrace : WordTrace (prefixWord ++ tailWord_682234) baseStart_682234 baseEnd_682234 := by
    simpa [prefixWord, tailWord_682234, baseEnd_682234] using wordTrace_append hprefix tailTrace_682234
  have hstable : (prefixWord ++ tailWord_682234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682234).length < 2 ^ (prefixWord ++ tailWord_682234).sum := by decide
  have hdescent : baseEnd_682234 < baseStart_682234 := by decide
  rcases family_descends (prefixWord ++ tailWord_682234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682240 : List Nat := [2, 1, 1, 2, 1, 1, 6, 9]
def baseStart_682240 : Nat := 118140960795 + 682240 * 2 ^ 59
def prefixEnd_682240 : Nat := 4983230072969 + 3 ^ 40 * 682240 * 2
def baseEnd_682240 : Nat := 12974705249019109872683

theorem tailTrace_682240 : CollatzResearch.WordTrace tailWord_682240 prefixEnd_682240 12974705249019109872683 := by
  unfold tailWord_682240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441668524184236080346087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16588891365578981440461449 12441668524184236080346087)
  ·
    refine ⟨18662502786276354120519131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12441668524184236080346087 18662502786276354120519131)
    ·
      refine ⟨27993754179414531180778697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18662502786276354120519131 27993754179414531180778697)
      ·
        refine ⟨20995315634560898385584023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27993754179414531180778697 20995315634560898385584023)
        ·
          refine ⟨31492973451841347578376035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20995315634560898385584023 31492973451841347578376035)
          ·
            refine ⟨47239460177762021367564053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31492973451841347578376035 47239460177762021367564053)
            ·
              refine ⟨2214349695832594751604565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47239460177762021367564053 2214349695832594751604565)
              ·
                refine ⟨12974705249019109872683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2214349695832594751604565 12974705249019109872683)
                ·
                  rfl

theorem cell23_682240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 9].length) (baseStart_682240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682240 prefixEnd_682240 := by exact prefixLift 682240
  have htrace : WordTrace (prefixWord ++ tailWord_682240) baseStart_682240 baseEnd_682240 := by
    simpa [prefixWord, tailWord_682240, baseEnd_682240] using wordTrace_append hprefix tailTrace_682240
  have hstable : (prefixWord ++ tailWord_682240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682240).length < 2 ^ (prefixWord ++ tailWord_682240).sum := by decide
  have hdescent : baseEnd_682240 < baseStart_682240 := by decide
  rcases family_descends (prefixWord ++ tailWord_682240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682244 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_682244 : Nat := 118140960795 + 682244 * 2 ^ 59
def prefixEnd_682244 : Nat := 4983230072969 + 3 ^ 40 * 682244 * 2
def baseEnd_682244 : Nat := 116773031882044650304141

theorem tailTrace_682244 : CollatzResearch.WordTrace tailWord_682244 prefixEnd_682244 116773031882044650304141 := by
  unfold tailWord_682244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441741470176990421918893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16588988626902653895891857 12441741470176990421918893)
  ·
    refine ⟨4665653051316371408219585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12441741470176990421918893 4665653051316371408219585)
    ·
      refine ⟨3499239788487278556164689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4665653051316371408219585 3499239788487278556164689)
      ·
        refine ⟨2624429841365458917123517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3499239788487278556164689 2624429841365458917123517)
        ·
          refine ⟨984161190512047093921319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2624429841365458917123517 984161190512047093921319)
          ·
            refine ⟨1476241785768070640881979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984161190512047093921319 1476241785768070640881979)
            ·
              refine ⟨2214362678652105961322969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476241785768070640881979 2214362678652105961322969)
              ·
                refine ⟨1660772008989079470992227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214362678652105961322969 1660772008989079470992227)
                ·
                  refine ⟨2491158013483619206488341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660772008989079470992227 2491158013483619206488341)
                  ·
                    refine ⟨116773031882044650304141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2491158013483619206488341 116773031882044650304141)
                    ·
                      rfl

theorem cell23_682244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_682244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682244 prefixEnd_682244 := by exact prefixLift 682244
  have htrace : WordTrace (prefixWord ++ tailWord_682244) baseStart_682244 baseEnd_682244 := by
    simpa [prefixWord, tailWord_682244, baseEnd_682244] using wordTrace_append hprefix tailTrace_682244
  have hstable : (prefixWord ++ tailWord_682244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682244).length < 2 ^ (prefixWord ++ tailWord_682244).sum := by decide
  have hdescent : baseEnd_682244 < baseStart_682244 := by decide
  rcases family_descends (prefixWord ++ tailWord_682244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682274 : List Nat := [3, 3, 1, 1, 3, 3, 1, 8]
def baseStart_682274 : Nat := 118140960795 + 682274 * 2 ^ 59
def prefixEnd_682274 : Nat := 4983230072969 + 3 ^ 40 * 682274 * 2
def baseEnd_682274 : Nat := 12975351854287734575455

theorem tailTrace_682274 : CollatzResearch.WordTrace tailWord_682274 prefixEnd_682274 12975351854287734575455 := by
  unfold tailWord_682274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221144282561323991857469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16589718086830197311619917 6221144282561323991857469)
  ·
    refine ⟨2332929105960496496946551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6221144282561323991857469 2332929105960496496946551)
    ·
      refine ⟨3499393658940744745419827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332929105960496496946551 3499393658940744745419827)
      ·
        refine ⟨5249090488411117118129741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499393658940744745419827 5249090488411117118129741)
        ·
          refine ⟨1968408933154168919298653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5249090488411117118129741 1968408933154168919298653)
          ·
            refine ⟨738153349932813344736995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1968408933154168919298653 738153349932813344736995)
            ·
              refine ⟨1107230024899220017105493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738153349932813344736995 1107230024899220017105493)
              ·
                refine ⟨12975351854287734575455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1107230024899220017105493 12975351854287734575455)
                ·
                  rfl

theorem cell23_682274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_682274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682274 prefixEnd_682274 := by exact prefixLift 682274
  have htrace : WordTrace (prefixWord ++ tailWord_682274) baseStart_682274 baseEnd_682274 := by
    simpa [prefixWord, tailWord_682274, baseEnd_682274] using wordTrace_append hprefix tailTrace_682274
  have hstable : (prefixWord ++ tailWord_682274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682274).length < 2 ^ (prefixWord ++ tailWord_682274).sum := by decide
  have hdescent : baseEnd_682274 < baseStart_682274 := by decide
  rcases family_descends (prefixWord ++ tailWord_682274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682285 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_682285 : Nat := 118140960795 + 682285 * 2 ^ 59
def prefixEnd_682285 : Nat := 4983230072969 + 3 ^ 40 * 682285 * 2
def baseEnd_682285 : Nat := 350340148352968290499735

theorem tailTrace_682285 : CollatzResearch.WordTrace tailWord_682285 prefixEnd_682285 350340148352968290499735 := by
  unfold tailWord_682285
  simp only [CollatzResearch.WordTrace]
  refine ⟨24884978333205444846080309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16589985555470296564053539 24884978333205444846080309)
  ·
    refine ⟨2332966718738010454320029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24884978333205444846080309 2332966718738010454320029)
    ·
      refine ⟨874862519526753920370011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2332966718738010454320029 874862519526753920370011)
      ·
        refine ⟨1312293779290130880555017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874862519526753920370011 1312293779290130880555017)
        ·
          refine ⟨984220334467598160416263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312293779290130880555017 984220334467598160416263)
          ·
            refine ⟨1476330501701397240624395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984220334467598160416263 1476330501701397240624395)
            ·
              refine ⟨2214495752552095860936593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476330501701397240624395 2214495752552095860936593)
              ·
                refine ⟨1660871814414071895702445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214495752552095860936593 1660871814414071895702445)
                ·
                  refine ⟨622826930405276960888417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1660871814414071895702445 622826930405276960888417)
                  ·
                    refine ⟨467120197803957720666313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 622826930405276960888417 467120197803957720666313)
                    ·
                      refine ⟨350340148352968290499735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467120197803957720666313 350340148352968290499735)
                      ·
                        rfl

theorem cell23_682285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_682285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682285 prefixEnd_682285 := by exact prefixLift 682285
  have htrace : WordTrace (prefixWord ++ tailWord_682285) baseStart_682285 baseEnd_682285 := by
    simpa [prefixWord, tailWord_682285, baseEnd_682285] using wordTrace_append hprefix tailTrace_682285
  have hstable : (prefixWord ++ tailWord_682285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682285).length < 2 ^ (prefixWord ++ tailWord_682285).sum := by decide
  have hdescent : baseEnd_682285 < baseStart_682285 := by decide
  rcases family_descends (prefixWord ++ tailWord_682285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682305 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_682305 : Nat := 118140960795 + 682305 * 2 ^ 59
def prefixEnd_682305 : Nat := 4983230072969 + 3 ^ 40 * 682305 * 2
def baseEnd_682305 : Nat := 350350417966058212249643

theorem tailTrace_682305 : CollatzResearch.WordTrace tailWord_682305 prefixEnd_682305 350350417966058212249643 := by
  unfold tailWord_682305
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885707793132988261808369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16590471862088658841205579 24885707793132988261808369)
  ·
    refine ⟨18664280844849741196356277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24885707793132988261808369 18664280844849741196356277)
    ·
      refine ⟨1749776329204663237158401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18664280844849741196356277 1749776329204663237158401)
      ·
        refine ⟨1312332246903497427868801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749776329204663237158401 1312332246903497427868801)
        ·
          refine ⟨984249185177623070901601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312332246903497427868801 984249185177623070901601)
          ·
            refine ⟨738186888883217303176201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984249185177623070901601 738186888883217303176201)
            ·
              refine ⟨553640166662412977382151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738186888883217303176201 553640166662412977382151)
              ·
                refine ⟨830460249993619466073227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553640166662412977382151 830460249993619466073227)
                ·
                  refine ⟨1245690374990429199109841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830460249993619466073227 1245690374990429199109841)
                  ·
                    refine ⟨934267781242821899332381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1245690374990429199109841 934267781242821899332381)
                    ·
                      refine ⟨350350417966058212249643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934267781242821899332381 350350417966058212249643)
                      ·
                        rfl

theorem cell23_682305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_682305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682305 prefixEnd_682305 := by exact prefixLift 682305
  have htrace : WordTrace (prefixWord ++ tailWord_682305) baseStart_682305 baseEnd_682305 := by
    simpa [prefixWord, tailWord_682305, baseEnd_682305] using wordTrace_append hprefix tailTrace_682305
  have hstable : (prefixWord ++ tailWord_682305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682305).length < 2 ^ (prefixWord ++ tailWord_682305).sum := by decide
  have hdescent : baseEnd_682305 < baseStart_682305 := by decide
  rcases family_descends (prefixWord ++ tailWord_682305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682311 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_682311 : Nat := 118140960795 + 682311 * 2 ^ 59
def prefixEnd_682311 : Nat := 4983230072969 + 3 ^ 40 * 682311 * 2
def baseEnd_682311 : Nat := 350353498849985188774615

theorem tailTrace_682311 : CollatzResearch.WordTrace tailWord_682311 prefixEnd_682311 350353498849985188774615 := by
  unfold tailWord_682311
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885926631111251286526787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16590617754074167524351191 24885926631111251286526787)
  ·
    refine ⟨37328889946666876929790181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24885926631111251286526787 37328889946666876929790181)
    ·
      refine ⟨6999166865000039424335659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37328889946666876929790181 6999166865000039424335659)
      ·
        refine ⟨10498750297500059136503489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999166865000039424335659 10498750297500059136503489)
        ·
          refine ⟨7874062723125044352377617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10498750297500059136503489 7874062723125044352377617)
          ·
            refine ⟨5905547042343783264283213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7874062723125044352377617 5905547042343783264283213)
            ·
              refine ⟨2214580140878918724106205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5905547042343783264283213 2214580140878918724106205)
              ·
                refine ⟨830467552829594521539827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2214580140878918724106205 830467552829594521539827)
                ·
                  refine ⟨1245701329244391782309741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830467552829594521539827 1245701329244391782309741)
                  ·
                    refine ⟨467137998466646918366153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245701329244391782309741 467137998466646918366153)
                    ·
                      refine ⟨350353498849985188774615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467137998466646918366153 350353498849985188774615)
                      ·
                        rfl

theorem cell23_682311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_682311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682311 prefixEnd_682311 := by exact prefixLift 682311
  have htrace : WordTrace (prefixWord ++ tailWord_682311) baseStart_682311 baseEnd_682311 := by
    simpa [prefixWord, tailWord_682311, baseEnd_682311] using wordTrace_append hprefix tailTrace_682311
  have hstable : (prefixWord ++ tailWord_682311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682311).length < 2 ^ (prefixWord ++ tailWord_682311).sum := by decide
  have hdescent : baseEnd_682311 < baseStart_682311 := by decide
  rcases family_descends (prefixWord ++ tailWord_682311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682341 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_682341 : Nat := 118140960795 + 682341 * 2 ^ 59
def prefixEnd_682341 : Nat := 4983230072969 + 3 ^ 40 * 682341 * 2
def baseEnd_682341 : Nat := 350368903269620071399477

theorem tailTrace_682341 : CollatzResearch.WordTrace tailWord_682341 prefixEnd_682341 350368903269620071399477 := by
  unfold tailWord_682341
  simp only [CollatzResearch.WordTrace]
  refine ⟨24887020821002566410118877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16591347214001710940079251 24887020821002566410118877)
  ·
    refine ⟨9332632807875962403794579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24887020821002566410118877 9332632807875962403794579)
    ·
      refine ⟨13998949211813943605691869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9332632807875962403794579 13998949211813943605691869)
      ·
        refine ⟨5249605954430228852134451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13998949211813943605691869 5249605954430228852134451)
        ·
          refine ⟨7874408931645343278201677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5249605954430228852134451 7874408931645343278201677)
          ·
            refine ⟨2952903349367003729325629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7874408931645343278201677 2952903349367003729325629)
            ·
              refine ⟨1107338756012626398497111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2952903349367003729325629 1107338756012626398497111)
              ·
                refine ⟨1661008134018939597745667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107338756012626398497111 1661008134018939597745667)
                ·
                  refine ⟨2491512201028409396618501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661008134018939597745667 2491512201028409396618501)
                  ·
                    refine ⟨467158537692826761865969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491512201028409396618501 467158537692826761865969)
                    ·
                      refine ⟨350368903269620071399477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467158537692826761865969 350368903269620071399477)
                      ·
                        rfl

theorem cell23_682341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_682341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682341 prefixEnd_682341 := by exact prefixLift 682341
  have htrace : WordTrace (prefixWord ++ tailWord_682341) baseStart_682341 baseEnd_682341 := by
    simpa [prefixWord, tailWord_682341, baseEnd_682341] using wordTrace_append hprefix tailTrace_682341
  have hstable : (prefixWord ++ tailWord_682341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682341).length < 2 ^ (prefixWord ++ tailWord_682341).sum := by decide
  have hdescent : baseEnd_682341 < baseStart_682341 := by decide
  rcases family_descends (prefixWord ++ tailWord_682341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682364 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 5]
def baseStart_682364 : Nat := 118140960795 + 682364 * 2 ^ 59
def prefixEnd_682364 : Nat := 4983230072969 + 3 ^ 40 * 682364 * 2
def baseEnd_682364 : Nat := 38931190369408164601319

theorem tailTrace_682364 : CollatzResearch.WordTrace tailWord_682364 prefixEnd_682364 38931190369408164601319 := by
  unfold tailWord_682364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443929849959620669103073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16591906466612827558804097 12443929849959620669103073)
  ·
    refine ⟨9332947387469715501827305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12443929849959620669103073 9332947387469715501827305)
    ·
      refine ⟨6999710540602286626370479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9332947387469715501827305 6999710540602286626370479)
      ·
        refine ⟨10499565810903429939555719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999710540602286626370479 10499565810903429939555719)
        ·
          refine ⟨15749348716355144909333579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10499565810903429939555719 15749348716355144909333579)
          ·
            refine ⟨23624023074532717364000369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15749348716355144909333579 23624023074532717364000369)
            ·
              refine ⟨17718017305899538023000277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23624023074532717364000369 17718017305899538023000277)
              ·
                refine ⟨415266030607020422414069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17718017305899538023000277 415266030607020422414069)
                ·
                  refine ⟨38931190369408164601319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415266030607020422414069 38931190369408164601319)
                  ·
                    rfl

theorem cell23_682364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_682364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682364 prefixEnd_682364 := by exact prefixLift 682364
  have htrace : WordTrace (prefixWord ++ tailWord_682364) baseStart_682364 baseEnd_682364 := by
    simpa [prefixWord, tailWord_682364, baseEnd_682364] using wordTrace_append hprefix tailTrace_682364
  have hstable : (prefixWord ++ tailWord_682364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682364).length < 2 ^ (prefixWord ++ tailWord_682364).sum := by decide
  have hdescent : baseEnd_682364 < baseStart_682364 := by decide
  rcases family_descends (prefixWord ++ tailWord_682364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682392 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_682392 : Nat := 118140960795 + 682392 * 2 ^ 59
def prefixEnd_682392 : Nat := 4983230072969 + 3 ^ 40 * 682392 * 2
def baseEnd_682392 : Nat := 350395090782999371861743

theorem tailTrace_682392 : CollatzResearch.WordTrace tailWord_682392 prefixEnd_682392 350395090782999371861743 := by
  unfold tailWord_682392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12444440471908901060112715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16592587295878534746816953 12444440471908901060112715)
  ·
    refine ⟨18666660707863351590169073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12444440471908901060112715 18666660707863351590169073)
    ·
      refine ⟨13999995530897513692626805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18666660707863351590169073 13999995530897513692626805)
      ·
        refine ⟨1312499581021641908683763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13999995530897513692626805 1312499581021641908683763)
        ·
          refine ⟨1968749371532462863025645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312499581021641908683763 1968749371532462863025645)
          ·
            refine ⟨738281014324673573634617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1968749371532462863025645 738281014324673573634617)
            ·
              refine ⟨553710760743505180225963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738281014324673573634617 553710760743505180225963)
              ·
                refine ⟨830566141115257770338945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553710760743505180225963 830566141115257770338945)
                ·
                  refine ⟨622924605836443327754209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830566141115257770338945 622924605836443327754209)
                  ·
                    refine ⟨467193454377332495815657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 622924605836443327754209 467193454377332495815657)
                    ·
                      refine ⟨350395090782999371861743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467193454377332495815657 350395090782999371861743)
                      ·
                        rfl

theorem cell23_682392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_682392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682392 prefixEnd_682392 := by exact prefixLift 682392
  have htrace : WordTrace (prefixWord ++ tailWord_682392) baseStart_682392 baseEnd_682392 := by
    simpa [prefixWord, tailWord_682392, baseEnd_682392] using wordTrace_append hprefix tailTrace_682392
  have hstable : (prefixWord ++ tailWord_682392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682392).length < 2 ^ (prefixWord ++ tailWord_682392).sum := by decide
  have hdescent : baseEnd_682392 < baseStart_682392 := by decide
  rcases family_descends (prefixWord ++ tailWord_682392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682427 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_682427 : Nat := 118140960795 + 682427 * 2 ^ 59
def prefixEnd_682427 : Nat := 4983230072969 + 3 ^ 40 * 682427 * 2
def baseEnd_682427 : Nat := 350413062605906734924081

theorem tailTrace_682427 : CollatzResearch.WordTrace tailWord_682427 prefixEnd_682427 350413062605906734924081 := by
  unfold tailWord_682427
  simp only [CollatzResearch.WordTrace]
  refine ⟨24890157498691003097749535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16593438332460668731833023 24890157498691003097749535)
  ·
    refine ⟨37335236248036504646624303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24890157498691003097749535 37335236248036504646624303)
    ·
      refine ⟨56002854372054756969936455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37335236248036504646624303 56002854372054756969936455)
      ·
        refine ⟨84004281558082135454904683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56002854372054756969936455 84004281558082135454904683)
        ·
          refine ⟨126006422337123203182357025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84004281558082135454904683 126006422337123203182357025)
          ·
            refine ⟨94504816752842402386767769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126006422337123203182357025 94504816752842402386767769)
            ·
              refine ⟨70878612564631801790075827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94504816752842402386767769 70878612564631801790075827)
              ·
                refine ⟨106317918846947702685113741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70878612564631801790075827 106317918846947702685113741)
                ·
                  refine ⟨39869219567605388506917653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106317918846947702685113741 39869219567605388506917653)
                  ·
                    refine ⟨1868869667231502586261765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39869219567605388506917653 1868869667231502586261765)
                    ·
                      refine ⟨350413062605906734924081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1868869667231502586261765 350413062605906734924081)
                      ·
                        rfl

theorem cell23_682427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_682427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682427 prefixEnd_682427 := by exact prefixLift 682427
  have htrace : WordTrace (prefixWord ++ tailWord_682427) baseStart_682427 baseEnd_682427 := by
    simpa [prefixWord, tailWord_682427, baseEnd_682427] using wordTrace_append hprefix tailTrace_682427
  have hstable : (prefixWord ++ tailWord_682427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682427).length < 2 ^ (prefixWord ++ tailWord_682427).sum := by decide
  have hdescent : baseEnd_682427 < baseStart_682427 := by decide
  rcases family_descends (prefixWord ++ tailWord_682427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682481 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_682481 : Nat := 118140960795 + 682481 * 2 ^ 59
def prefixEnd_682481 : Nat := 4983230072969 + 3 ^ 40 * 682481 * 2
def baseEnd_682481 : Nat := 350440790561249523648833

theorem tailTrace_682481 : CollatzResearch.WordTrace tailWord_682481 prefixEnd_682481 350440790561249523648833 := by
  unfold tailWord_682481
  simp only [CollatzResearch.WordTrace]
  refine ⟨24892127040495370320215297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16594751360330246880143531 24892127040495370320215297)
  ·
    refine ⟨18669095280371527740161473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24892127040495370320215297 18669095280371527740161473)
    ·
      refine ⟨14001821460278645805121105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18669095280371527740161473 14001821460278645805121105)
      ·
        refine ⟨10501366095208984353840829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14001821460278645805121105 10501366095208984353840829)
        ·
          refine ⟨3938012285703369132690311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10501366095208984353840829 3938012285703369132690311)
          ·
            refine ⟨5907018428555053699035467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938012285703369132690311 5907018428555053699035467)
            ·
              refine ⟨8860527642832580548553201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907018428555053699035467 8860527642832580548553201)
              ·
                refine ⟨6645395732124435411414901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8860527642832580548553201 6645395732124435411414901)
                ·
                  refine ⟨623005849886665819820147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6645395732124435411414901 623005849886665819820147)
                  ·
                    refine ⟨934508774829998729730221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623005849886665819820147 934508774829998729730221)
                    ·
                      refine ⟨350440790561249523648833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934508774829998729730221 350440790561249523648833)
                      ·
                        rfl

theorem cell23_682481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_682481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682481 prefixEnd_682481 := by exact prefixLift 682481
  have htrace : WordTrace (prefixWord ++ tailWord_682481) baseStart_682481 baseEnd_682481 := by
    simpa [prefixWord, tailWord_682481, baseEnd_682481] using wordTrace_append hprefix tailTrace_682481
  have hstable : (prefixWord ++ tailWord_682481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682481).length < 2 ^ (prefixWord ++ tailWord_682481).sum := by decide
  have hdescent : baseEnd_682481 < baseStart_682481 := by decide
  rcases family_descends (prefixWord ++ tailWord_682481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682531 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 4, 4]
def baseStart_682531 : Nat := 118140960795 + 682531 * 2 ^ 59
def prefixEnd_682531 : Nat := 4983230072969 + 3 ^ 40 * 682531 * 2
def baseEnd_682531 : Nat := 116822154864658109341201

theorem tailTrace_682531 : CollatzResearch.WordTrace tailWord_682531 prefixEnd_682531 116822154864658109341201 := by
  unfold tailWord_682531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24893950690314228859535447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16595967126876152573023631 24893950690314228859535447)
  ·
    refine ⟨37340926035471343289303171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24893950690314228859535447 37340926035471343289303171)
    ·
      refine ⟨56011389053207014933954757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37340926035471343289303171 56011389053207014933954757)
      ·
        refine ⟨10502135447476315300116517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56011389053207014933954757 10502135447476315300116517)
        ·
          refine ⟨1969150396401809118771847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10502135447476315300116517 1969150396401809118771847)
          ·
            refine ⟨2953725594602713678157771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969150396401809118771847 2953725594602713678157771)
            ·
              refine ⟨4430588391904070517236657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953725594602713678157771 4430588391904070517236657)
              ·
                refine ⟨3322941293928052887927493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430588391904070517236657 3322941293928052887927493)
                ·
                  refine ⟨623051492611509916486405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3322941293928052887927493 623051492611509916486405)
                  ·
                    refine ⟨116822154864658109341201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623051492611509916486405 116822154864658109341201)
                    ·
                      rfl

theorem cell23_682531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 4].length) (baseStart_682531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682531 prefixEnd_682531 := by exact prefixLift 682531
  have htrace : WordTrace (prefixWord ++ tailWord_682531) baseStart_682531 baseEnd_682531 := by
    simpa [prefixWord, tailWord_682531, baseEnd_682531] using wordTrace_append hprefix tailTrace_682531
  have hstable : (prefixWord ++ tailWord_682531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682531).length < 2 ^ (prefixWord ++ tailWord_682531).sum := by decide
  have hdescent : baseEnd_682531 < baseStart_682531 := by decide
  rcases family_descends (prefixWord ++ tailWord_682531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682538 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_682538 : Nat := 118140960795 + 682538 * 2 ^ 59
def prefixEnd_682538 : Nat := 4983230072969 + 3 ^ 40 * 682538 * 2
def baseEnd_682538 : Nat := 350470058958555800636071

theorem tailTrace_682538 : CollatzResearch.WordTrace tailWord_682538 prefixEnd_682538 350470058958555800636071 := by
  unfold tailWord_682538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223551500322217263760067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16596137334192579370026845 6223551500322217263760067)
  ·
    refine ⟨9335327250483325895640101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6223551500322217263760067 9335327250483325895640101)
    ·
      refine ⟨1750373859465623605432519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9335327250483325895640101 1750373859465623605432519)
      ·
        refine ⟨2625560789198435408148779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750373859465623605432519 2625560789198435408148779)
        ·
          refine ⟨3938341183797653112223169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625560789198435408148779 3938341183797653112223169)
          ·
            refine ⟨2953755887848239834167377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3938341183797653112223169 2953755887848239834167377)
            ·
              refine ⟨2215316915886179875625533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953755887848239834167377 2215316915886179875625533)
              ·
                refine ⟨830743843457317453359575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2215316915886179875625533 830743843457317453359575)
                ·
                  refine ⟨1246115765185976180039363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830743843457317453359575 1246115765185976180039363)
                  ·
                    refine ⟨1869173647778964270059045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246115765185976180039363 1869173647778964270059045)
                    ·
                      refine ⟨350470058958555800636071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1869173647778964270059045 350470058958555800636071)
                      ·
                        rfl

theorem cell23_682538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_682538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682538 prefixEnd_682538 := by exact prefixLift 682538
  have htrace : WordTrace (prefixWord ++ tailWord_682538) baseStart_682538 baseEnd_682538 := by
    simpa [prefixWord, tailWord_682538, baseEnd_682538] using wordTrace_append hprefix tailTrace_682538
  have hstable : (prefixWord ++ tailWord_682538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682538).length < 2 ^ (prefixWord ++ tailWord_682538).sum := by decide
  have hdescent : baseEnd_682538 < baseStart_682538 := by decide
  rcases family_descends (prefixWord ++ tailWord_682538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682561 : List Nat := [1, 2, 5, 1, 1, 3, 2, 8]
def baseStart_682561 : Nat := 118140960795 + 682561 * 2 ^ 59
def prefixEnd_682561 : Nat := 4983230072969 + 3 ^ 40 * 682561 * 2
def baseEnd_682561 : Nat := 12980809963467007801795

theorem tailTrace_682561 : CollatzResearch.WordTrace tailWord_682561 prefixEnd_682561 12980809963467007801795 := by
  unfold tailWord_682561
  simp only [CollatzResearch.WordTrace]
  refine ⟨24895044880205543983127537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16596696586803695988751691 24895044880205543983127537)
  ·
    refine ⟨18671283660154157987345653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24895044880205543983127537 18671283660154157987345653)
    ·
      refine ⟨1750432843139452311313655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18671283660154157987345653 1750432843139452311313655)
      ·
        refine ⟨2625649264709178466970483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750432843139452311313655 2625649264709178466970483)
        ·
          refine ⟨3938473897063767700455725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625649264709178466970483 3938473897063767700455725)
          ·
            refine ⟨1476927711398912887670897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3938473897063767700455725 1476927711398912887670897)
            ·
              refine ⟨1107695783549184665753173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476927711398912887670897 1107695783549184665753173)
              ·
                refine ⟨12980809963467007801795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1107695783549184665753173 12980809963467007801795)
                ·
                  rfl

theorem cell23_682561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 8].length) (baseStart_682561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682561 prefixEnd_682561 := by exact prefixLift 682561
  have htrace : WordTrace (prefixWord ++ tailWord_682561) baseStart_682561 baseEnd_682561 := by
    simpa [prefixWord, tailWord_682561, baseEnd_682561] using wordTrace_append hprefix tailTrace_682561
  have hstable : (prefixWord ++ tailWord_682561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682561).length < 2 ^ (prefixWord ++ tailWord_682561).sum := by decide
  have hdescent : baseEnd_682561 < baseStart_682561 := by decide
  rcases family_descends (prefixWord ++ tailWord_682561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682565 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_682565 : Nat := 118140960795 + 682565 * 2 ^ 59
def prefixEnd_682565 : Nat := 4983230072969 + 3 ^ 40 * 682565 * 2
def baseEnd_682565 : Nat := 116827974312075731666149

theorem tailTrace_682565 : CollatzResearch.WordTrace tailWord_682565 prefixEnd_682565 116827974312075731666149 := by
  unfold tailWord_682565
  simp only [CollatzResearch.WordTrace]
  refine ⟨24895190772191052666273149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16596793848127368444182099 24895190772191052666273149)
  ·
    refine ⟨9335696539571644749852431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24895190772191052666273149 9335696539571644749852431)
    ·
      refine ⟨14003544809357467124778647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9335696539571644749852431 14003544809357467124778647)
      ·
        refine ⟨21005317214036200687167971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003544809357467124778647 21005317214036200687167971)
        ·
          refine ⟨31507975821054301030751957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21005317214036200687167971 31507975821054301030751957)
          ·
            refine ⟨738468183305960180408249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31507975821054301030751957 738468183305960180408249)
            ·
              refine ⟨553851137479470135306187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738468183305960180408249 553851137479470135306187)
              ·
                refine ⟨830776706219205202959281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553851137479470135306187 830776706219205202959281)
                ·
                  refine ⟨623082529664403902219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830776706219205202959281 623082529664403902219461)
                  ·
                    refine ⟨116827974312075731666149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623082529664403902219461 116827974312075731666149)
                    ·
                      rfl

theorem cell23_682565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_682565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682565 prefixEnd_682565 := by exact prefixLift 682565
  have htrace : WordTrace (prefixWord ++ tailWord_682565) baseStart_682565 baseEnd_682565 := by
    simpa [prefixWord, tailWord_682565, baseEnd_682565] using wordTrace_append hprefix tailTrace_682565
  have hstable : (prefixWord ++ tailWord_682565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682565).length < 2 ^ (prefixWord ++ tailWord_682565).sum := by decide
  have hdescent : baseEnd_682565 < baseStart_682565 := by decide
  rcases family_descends (prefixWord ++ tailWord_682565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682584 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_682584 : Nat := 118140960795 + 682584 * 2 ^ 59
def prefixEnd_682584 : Nat := 4983230072969 + 3 ^ 40 * 682584 * 2
def baseEnd_682584 : Nat := 350493679068662620660859

theorem tailTrace_682584 : CollatzResearch.WordTrace tailWord_682584 prefixEnd_682584 350493679068662620660859 := by
  unfold tailWord_682584
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447941879561109455607403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16597255839414812607476537 12447941879561109455607403)
  ·
    refine ⟨18671912819341664183411105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12447941879561109455607403 18671912819341664183411105)
    ·
      refine ⟨14003934614506248137558329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18671912819341664183411105 14003934614506248137558329)
      ·
        refine ⟨10502950960879686103168747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14003934614506248137558329 10502950960879686103168747)
        ·
          refine ⟨15754426441319529154753121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10502950960879686103168747 15754426441319529154753121)
          ·
            refine ⟨11815819830989646866064841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15754426441319529154753121 11815819830989646866064841)
            ·
              refine ⟨8861864873242235149548631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11815819830989646866064841 8861864873242235149548631)
              ·
                refine ⟨13292797309863352724322947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8861864873242235149548631 13292797309863352724322947)
                ·
                  refine ⟨19939195964795029086484421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13292797309863352724322947 19939195964795029086484421)
                  ·
                    refine ⟨3738599243399067953715829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19939195964795029086484421 3738599243399067953715829)
                    ·
                      refine ⟨350493679068662620660859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3738599243399067953715829 350493679068662620660859)
                      ·
                        rfl

theorem cell23_682584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_682584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682584 prefixEnd_682584 := by exact prefixLift 682584
  have htrace : WordTrace (prefixWord ++ tailWord_682584) baseStart_682584 baseEnd_682584 := by
    simpa [prefixWord, tailWord_682584, baseEnd_682584] using wordTrace_append hprefix tailTrace_682584
  have hstable : (prefixWord ++ tailWord_682584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682584).length < 2 ^ (prefixWord ++ tailWord_682584).sum := by decide
  have hdescent : baseEnd_682584 < baseStart_682584 := by decide
  rcases family_descends (prefixWord ++ tailWord_682584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682605 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_682605 : Nat := 118140960795 + 682605 * 2 ^ 59
def prefixEnd_682605 : Nat := 4983230072969 + 3 ^ 40 * 682605 * 2
def baseEnd_682605 : Nat := 350504462162407038498263

theorem tailTrace_682605 : CollatzResearch.WordTrace tailWord_682605 prefixEnd_682605 350504462162407038498263 := by
  unfold tailWord_682605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24896649692046139497729269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16597766461364092998486179 24896649692046139497729269)
  ·
    refine ⟨2334060908629325577912119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24896649692046139497729269 2334060908629325577912119)
    ·
      refine ⟨3501091362943988366868179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2334060908629325577912119 3501091362943988366868179)
      ·
        refine ⟨5251637044415982550302269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501091362943988366868179 5251637044415982550302269)
        ·
          refine ⟨1969363891655993456363351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5251637044415982550302269 1969363891655993456363351)
          ·
            refine ⟨2954045837483990184545027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969363891655993456363351 2954045837483990184545027)
            ·
              refine ⟨4431068756225985276817541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954045837483990184545027 4431068756225985276817541)
              ·
                refine ⟨830825391792372239403289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4431068756225985276817541 830825391792372239403289)
                ·
                  refine ⟨623119043844279179552467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830825391792372239403289 623119043844279179552467)
                  ·
                    refine ⟨934678565766418769328701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623119043844279179552467 934678565766418769328701)
                    ·
                      refine ⟨350504462162407038498263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934678565766418769328701 350504462162407038498263)
                      ·
                        rfl

theorem cell23_682605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_682605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682605 prefixEnd_682605 := by exact prefixLift 682605
  have htrace : WordTrace (prefixWord ++ tailWord_682605) baseStart_682605 baseEnd_682605 := by
    simpa [prefixWord, tailWord_682605, baseEnd_682605] using wordTrace_append hprefix tailTrace_682605
  have hstable : (prefixWord ++ tailWord_682605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682605).length < 2 ^ (prefixWord ++ tailWord_682605).sum := by decide
  have hdescent : baseEnd_682605 < baseStart_682605 := by decide
  rcases family_descends (prefixWord ++ tailWord_682605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682606 : List Nat := [4, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_682606 : Nat := 118140960795 + 682606 * 2 ^ 59
def prefixEnd_682606 : Nat := 4983230072969 + 3 ^ 40 * 682606 * 2
def baseEnd_682606 : Nat := 350504975643061534585759

theorem tailTrace_682606 : CollatzResearch.WordTrace tailWord_682606 prefixEnd_682606 350504975643061534585759 := by
  unfold tailWord_682606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112085770630314583564459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16597790776695011112343781 3112085770630314583564459)
  ·
    refine ⟨4668128655945471875346689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3112085770630314583564459 4668128655945471875346689)
    ·
      refine ⟨3501096491959103906510017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4668128655945471875346689 3501096491959103906510017)
      ·
        refine ⟨2625822368969327929882513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3501096491959103906510017 2625822368969327929882513)
        ·
          refine ⟨1969366776726995947411885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625822368969327929882513 1969366776726995947411885)
          ·
            refine ⟨738512541272623480279457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1969366776726995947411885 738512541272623480279457)
            ·
              refine ⟨553884405954467610209593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738512541272623480279457 553884405954467610209593)
              ·
                refine ⟨415413304465850707657195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553884405954467610209593 415413304465850707657195)
                ·
                  refine ⟨623119956698776061485793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415413304465850707657195 623119956698776061485793)
                  ·
                    refine ⟨467339967524082046114345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623119956698776061485793 467339967524082046114345)
                    ·
                      refine ⟨350504975643061534585759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467339967524082046114345 350504975643061534585759)
                      ·
                        rfl

theorem cell23_682606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_682606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682606 prefixEnd_682606 := by exact prefixLift 682606
  have htrace : WordTrace (prefixWord ++ tailWord_682606) baseStart_682606 baseEnd_682606 := by
    simpa [prefixWord, tailWord_682606, baseEnd_682606] using wordTrace_append hprefix tailTrace_682606
  have hstable : (prefixWord ++ tailWord_682606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682606).length < 2 ^ (prefixWord ++ tailWord_682606).sum := by decide
  have hdescent : baseEnd_682606 < baseStart_682606 := by decide
  rcases family_descends (prefixWord ++ tailWord_682606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682631 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_682631 : Nat := 118140960795 + 682631 * 2 ^ 59
def prefixEnd_682631 : Nat := 4983230072969 + 3 ^ 40 * 682631 * 2
def baseEnd_682631 : Nat := 350517812659423936773143

theorem tailTrace_682631 : CollatzResearch.WordTrace tailWord_682631 prefixEnd_682631 350517812659423936773143 := by
  unfold tailWord_682631
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897597989951945938175747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16598398659967963958783831 24897597989951945938175747)
  ·
    refine ⟨37346396984927918907263621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24897597989951945938175747 37346396984927918907263621)
    ·
      refine ⟨7002449434673984795111929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37346396984927918907263621 7002449434673984795111929)
      ·
        refine ⟨5251837076005488596333947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7002449434673984795111929 5251837076005488596333947)
        ·
          refine ⟨7877755614008232894500921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251837076005488596333947 7877755614008232894500921)
          ·
            refine ⟨5908316710506174670875691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7877755614008232894500921 5908316710506174670875691)
            ·
              refine ⟨8862475065759262006313537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908316710506174670875691 8862475065759262006313537)
              ·
                refine ⟨6646856299319446504735153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8862475065759262006313537 6646856299319446504735153)
                ·
                  refine ⟨4985142224489584878551365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6646856299319446504735153 4985142224489584878551365)
                  ·
                    refine ⟨934714167091797164728381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4985142224489584878551365 934714167091797164728381)
                    ·
                      refine ⟨350517812659423936773143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934714167091797164728381 350517812659423936773143)
                      ·
                        rfl

theorem cell23_682631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_682631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682631 prefixEnd_682631 := by exact prefixLift 682631
  have htrace : WordTrace (prefixWord ++ tailWord_682631) baseStart_682631 baseEnd_682631 := by
    simpa [prefixWord, tailWord_682631, baseEnd_682631] using wordTrace_append hprefix tailTrace_682631
  have hstable : (prefixWord ++ tailWord_682631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682631).length < 2 ^ (prefixWord ++ tailWord_682631).sum := by decide
  have hdescent : baseEnd_682631 < baseStart_682631 := by decide
  rcases family_descends (prefixWord ++ tailWord_682631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682679 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_682679 : Nat := 118140960795 + 682679 * 2 ^ 59
def prefixEnd_682679 : Nat := 4983230072969 + 3 ^ 40 * 682679 * 2
def baseEnd_682679 : Nat := 350542459730839748972923

theorem tailTrace_682679 : CollatzResearch.WordTrace tailWord_682679 prefixEnd_682679 350542459730839748972923 := by
  unfold tailWord_682679
  simp only [CollatzResearch.WordTrace]
  refine ⟨24899348693778050135923091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16599565795852033423948727 24899348693778050135923091)
  ·
    refine ⟨37349023040667075203884637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24899348693778050135923091 37349023040667075203884637)
    ·
      refine ⟨14005883640250153201456739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37349023040667075203884637 14005883640250153201456739)
      ·
        refine ⟨21008825460375229802185109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14005883640250153201456739 21008825460375229802185109)
        ·
          refine ⟨984788693455088896977427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21008825460375229802185109 984788693455088896977427)
          ·
            refine ⟨1477183040182633345466141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984788693455088896977427 1477183040182633345466141)
            ·
              refine ⟨553943640068487504549803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1477183040182633345466141 553943640068487504549803)
              ·
                refine ⟨830915460102731256824705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553943640068487504549803 830915460102731256824705)
                ·
                  refine ⟨623186595077048442618529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830915460102731256824705 623186595077048442618529)
                  ·
                    refine ⟨467389946307786331963897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623186595077048442618529 467389946307786331963897)
                    ·
                      refine ⟨350542459730839748972923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467389946307786331963897 350542459730839748972923)
                      ·
                        rfl

theorem cell23_682679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_682679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682679 prefixEnd_682679 := by exact prefixLift 682679
  have htrace : WordTrace (prefixWord ++ tailWord_682679) baseStart_682679 baseEnd_682679 := by
    simpa [prefixWord, tailWord_682679, baseEnd_682679] using wordTrace_append hprefix tailTrace_682679
  have hstable : (prefixWord ++ tailWord_682679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682679).length < 2 ^ (prefixWord ++ tailWord_682679).sum := by decide
  have hdescent : baseEnd_682679 < baseStart_682679 := by decide
  rcases family_descends (prefixWord ++ tailWord_682679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682775 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 6]
def baseStart_682775 : Nat := 118140960795 + 682775 * 2 ^ 59
def prefixEnd_682775 : Nat := 4983230072969 + 3 ^ 40 * 682775 * 2
def baseEnd_682775 : Nat := 38954639319296819263609

theorem tailTrace_682775 : CollatzResearch.WordTrace tailWord_682775 prefixEnd_682775 38954639319296819263609 := by
  unfold tailWord_682775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24902850101430258531417779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16601900067620172354278519 24902850101430258531417779)
  ·
    refine ⟨37354275152145387797126669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24902850101430258531417779 37354275152145387797126669)
    ·
      refine ⟨14007853182054520423922501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37354275152145387797126669 14007853182054520423922501)
      ·
        refine ⟨2626472471635222579485469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14007853182054520423922501 2626472471635222579485469)
        ·
          refine ⟨984927176863208467307051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2626472471635222579485469 984927176863208467307051)
          ·
            refine ⟨1477390765294812700960577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984927176863208467307051 1477390765294812700960577)
            ·
              refine ⟨1108043073971109525720433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477390765294812700960577 1108043073971109525720433)
              ·
                refine ⟨831032305478332144290325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108043073971109525720433 831032305478332144290325)
                ·
                  refine ⟨38954639319296819263609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 831032305478332144290325 38954639319296819263609)
                  ·
                    rfl

theorem cell23_682775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 6].length) (baseStart_682775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682775 prefixEnd_682775 := by exact prefixLift 682775
  have htrace : WordTrace (prefixWord ++ tailWord_682775) baseStart_682775 baseEnd_682775 := by
    simpa [prefixWord, tailWord_682775, baseEnd_682775] using wordTrace_append hprefix tailTrace_682775
  have hstable : (prefixWord ++ tailWord_682775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682775).length < 2 ^ (prefixWord ++ tailWord_682775).sum := by decide
  have hdescent : baseEnd_682775 < baseStart_682775 := by decide
  rcases family_descends (prefixWord ++ tailWord_682775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682785 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_682785 : Nat := 118140960795 + 682785 * 2 ^ 59
def prefixEnd_682785 : Nat := 4983230072969 + 3 ^ 40 * 682785 * 2
def baseEnd_682785 : Nat := 350596888680216334247435

theorem tailTrace_682785 : CollatzResearch.WordTrace tailWord_682785 prefixEnd_682785 350596888680216334247435 := by
  unfold tailWord_682785
  simp only [CollatzResearch.WordTrace]
  refine ⟨24903214831394030239281809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16602143220929353492854539 24903214831394030239281809)
  ·
    refine ⟨18677411123545522679461357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24903214831394030239281809 18677411123545522679461357)
    ·
      refine ⟨7004029171329571004798009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18677411123545522679461357 7004029171329571004798009)
      ·
        refine ⟨5253021878497178253598507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7004029171329571004798009 5253021878497178253598507)
        ·
          refine ⟨7879532817745767380397761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253021878497178253598507 7879532817745767380397761)
          ·
            refine ⟨5909649613309325535298321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7879532817745767380397761 5909649613309325535298321)
            ·
              refine ⟨4432237209981994151473741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5909649613309325535298321 4432237209981994151473741)
              ·
                refine ⟨1662088953743247806802653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4432237209981994151473741 1662088953743247806802653)
                ·
                  refine ⟨623283357653717927550995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662088953743247806802653 623283357653717927550995)
                  ·
                    refine ⟨934925036480576891326493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623283357653717927550995 934925036480576891326493)
                    ·
                      refine ⟨350596888680216334247435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934925036480576891326493 350596888680216334247435)
                      ·
                        rfl

theorem cell23_682785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_682785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682785 prefixEnd_682785 := by exact prefixLift 682785
  have htrace : WordTrace (prefixWord ++ tailWord_682785) baseStart_682785 baseEnd_682785 := by
    simpa [prefixWord, tailWord_682785, baseEnd_682785] using wordTrace_append hprefix tailTrace_682785
  have hstable : (prefixWord ++ tailWord_682785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682785).length < 2 ^ (prefixWord ++ tailWord_682785).sum := by decide
  have hdescent : baseEnd_682785 < baseStart_682785 := by decide
  rcases family_descends (prefixWord ++ tailWord_682785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682806 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_682806 : Nat := 118140960795 + 682806 * 2 ^ 59
def prefixEnd_682806 : Nat := 4983230072969 + 3 ^ 40 * 682806 * 2
def baseEnd_682806 : Nat := 350607671773960752084839

theorem tailTrace_682806 : CollatzResearch.WordTrace tailWord_682806 prefixEnd_682806 350607671773960752084839 := by
  unfold tailWord_682806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556498797769871926612267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16602653842878633883864181 1556498797769871926612267)
  ·
    refine ⟨2334748196654807889918401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556498797769871926612267 2334748196654807889918401)
    ·
      refine ⟨1751061147491105917438801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334748196654807889918401 1751061147491105917438801)
      ·
        refine ⟨1313295860618329438079101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1751061147491105917438801 1313295860618329438079101)
        ·
          refine ⟨492485947731873539279663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1313295860618329438079101 492485947731873539279663)
          ·
            refine ⟨738728921597810308919495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492485947731873539279663 738728921597810308919495)
            ·
              refine ⟨1108093382396715463379243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738728921597810308919495 1108093382396715463379243)
              ·
                refine ⟨1662140073595073195068865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108093382396715463379243 1662140073595073195068865)
                ·
                  refine ⟨1246605055196304896301649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1662140073595073195068865 1246605055196304896301649)
                  ·
                    refine ⟨934953791397228672226237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1246605055196304896301649 934953791397228672226237)
                    ·
                      refine ⟨350607671773960752084839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 934953791397228672226237 350607671773960752084839)
                      ·
                        rfl

theorem cell23_682806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_682806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682806 prefixEnd_682806 := by exact prefixLift 682806
  have htrace : WordTrace (prefixWord ++ tailWord_682806) baseStart_682806 baseEnd_682806 := by
    simpa [prefixWord, tailWord_682806, baseEnd_682806] using wordTrace_append hprefix tailTrace_682806
  have hstable : (prefixWord ++ tailWord_682806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682806).length < 2 ^ (prefixWord ++ tailWord_682806).sum := by decide
  have hdescent : baseEnd_682806 < baseStart_682806 := by decide
  rcases family_descends (prefixWord ++ tailWord_682806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682808 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_682808 : Nat := 118140960795 + 682808 * 2 ^ 59
def prefixEnd_682808 : Nat := 4983230072969 + 3 ^ 40 * 682808 * 2
def baseEnd_682808 : Nat := 350608698735269744259829

theorem tailTrace_682808 : CollatzResearch.WordTrace tailWord_682808 prefixEnd_682808 350608698735269744259829 := by
  unfold tailWord_682808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452026855155352583684539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16602702473540470111579385 12452026855155352583684539)
  ·
    refine ⟨18678040282733028875526809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452026855155352583684539 18678040282733028875526809)
    ·
      refine ⟨14008530212049771656645107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18678040282733028875526809 14008530212049771656645107)
      ·
        refine ⟨21012795318074657484967661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14008530212049771656645107 21012795318074657484967661)
        ·
          refine ⟨7879798244277996556862873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21012795318074657484967661 7879798244277996556862873)
          ·
            refine ⟨5909848683208497417647155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7879798244277996556862873 5909848683208497417647155)
            ·
              refine ⟨8864773024812746126470733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909848683208497417647155 8864773024812746126470733)
              ·
                refine ⟨3324289884304779797426525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8864773024812746126470733 3324289884304779797426525)
                ·
                  refine ⟨1246608706614292424034947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3324289884304779797426525 1246608706614292424034947)
                  ·
                    refine ⟨1869913059921438636052421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246608706614292424034947 1869913059921438636052421)
                    ·
                      refine ⟨350608698735269744259829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1869913059921438636052421 350608698735269744259829)
                      ·
                        rfl

theorem cell23_682808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_682808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682808 prefixEnd_682808 := by exact prefixLift 682808
  have htrace : WordTrace (prefixWord ++ tailWord_682808) baseStart_682808 baseEnd_682808 := by
    simpa [prefixWord, tailWord_682808, baseEnd_682808] using wordTrace_append hprefix tailTrace_682808
  have hstable : (prefixWord ++ tailWord_682808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682808).length < 2 ^ (prefixWord ++ tailWord_682808).sum := by decide
  have hdescent : baseEnd_682808 < baseStart_682808 := by decide
  rcases family_descends (prefixWord ++ tailWord_682808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682825 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 4]
def baseStart_682825 : Nat := 118140960795 + 682825 * 2 ^ 59
def prefixEnd_682825 : Nat := 4983230072969 + 3 ^ 40 * 682825 * 2
def baseEnd_682825 : Nat := 350617427906396177747251

theorem tailTrace_682825 : CollatzResearch.WordTrace tailWord_682825 prefixEnd_682825 350617427906396177747251 := by
  unfold tailWord_682825
  simp only [CollatzResearch.WordTrace]
  refine ⟨24904673751249117070737929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16603115834166078047158619 24904673751249117070737929)
  ·
    refine ⟨18678505313436837803053447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24904673751249117070737929 18678505313436837803053447)
    ·
      refine ⟨28017757970155256704580171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678505313436837803053447 28017757970155256704580171)
      ·
        refine ⟨42026636955232885056870257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28017757970155256704580171 42026636955232885056870257)
        ·
          refine ⟨31519977716424663792652693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42026636955232885056870257 31519977716424663792652693)
          ·
            refine ⟨1477498955457406115280595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31519977716424663792652693 1477498955457406115280595)
            ·
              refine ⟨2216248433186109172920893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477498955457406115280595 2216248433186109172920893)
              ·
                refine ⟨831093162444790939845335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2216248433186109172920893 831093162444790939845335)
                ·
                  refine ⟨1246639743667186409768003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831093162444790939845335 1246639743667186409768003)
                  ·
                    refine ⟨1869959615500779614652005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246639743667186409768003 1869959615500779614652005)
                    ·
                      refine ⟨350617427906396177747251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1869959615500779614652005 350617427906396177747251)
                      ·
                        rfl

theorem cell23_682825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_682825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682825 prefixEnd_682825 := by exact prefixLift 682825
  have htrace : WordTrace (prefixWord ++ tailWord_682825) baseStart_682825 baseEnd_682825 := by
    simpa [prefixWord, tailWord_682825, baseEnd_682825] using wordTrace_append hprefix tailTrace_682825
  have hstable : (prefixWord ++ tailWord_682825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682825).length < 2 ^ (prefixWord ++ tailWord_682825).sum := by decide
  have hdescent : baseEnd_682825 < baseStart_682825 := by decide
  rcases family_descends (prefixWord ++ tailWord_682825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682842 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_682842 : Nat := 118140960795 + 682842 * 2 ^ 59
def prefixEnd_682842 : Nat := 4983230072969 + 3 ^ 40 * 682842 * 2
def baseEnd_682842 : Nat := 350626157077522611234673

theorem tailTrace_682842 : CollatzResearch.WordTrace tailWord_682842 prefixEnd_682842 350626157077522611234673 := by
  unfold tailWord_682842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226323448046882243526695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16603529194791685982737853 6226323448046882243526695)
  ·
    refine ⟨9339485172070323365290043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6226323448046882243526695 9339485172070323365290043)
    ·
      refine ⟨14009227758105485047935065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9339485172070323365290043 14009227758105485047935065)
      ·
        refine ⟨10506920818579113785951299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14009227758105485047935065 10506920818579113785951299)
        ·
          refine ⟨15760381227868670678926949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10506920818579113785951299 15760381227868670678926949)
          ·
            refine ⟨2955071480225375752298803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15760381227868670678926949 2955071480225375752298803)
            ·
              refine ⟨4432607220338063628448205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955071480225375752298803 4432607220338063628448205)
              ·
                refine ⟨1662227707626773860668077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4432607220338063628448205 1662227707626773860668077)
                ·
                  refine ⟨623335390360040197750529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662227707626773860668077 623335390360040197750529)
                  ·
                    refine ⟨467501542770030148312897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623335390360040197750529 467501542770030148312897)
                    ·
                      refine ⟨350626157077522611234673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467501542770030148312897 350626157077522611234673)
                      ·
                        rfl

theorem cell23_682842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_682842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682842 prefixEnd_682842 := by exact prefixLift 682842
  have htrace : WordTrace (prefixWord ++ tailWord_682842) baseStart_682842 baseEnd_682842 := by
    simpa [prefixWord, tailWord_682842, baseEnd_682842] using wordTrace_append hprefix tailTrace_682842
  have hstable : (prefixWord ++ tailWord_682842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682842).length < 2 ^ (prefixWord ++ tailWord_682842).sum := by decide
  have hdescent : baseEnd_682842 < baseStart_682842 := by decide
  rcases family_descends (prefixWord ++ tailWord_682842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682855 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_682855 : Nat := 118140960795 + 682855 * 2 ^ 59
def prefixEnd_682855 : Nat := 4983230072969 + 3 ^ 40 * 682855 * 2
def baseEnd_682855 : Nat := 350632832326031060372113

theorem tailTrace_682855 : CollatzResearch.WordTrace tailWord_682855 prefixEnd_682855 350632832326031060372113 := by
  unfold tailWord_682855
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905767941140432194330019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16603845294093621462886679 24905767941140432194330019)
  ·
    refine ⟨37358651911710648291495029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24905767941140432194330019 37358651911710648291495029)
    ·
      refine ⟨3502373616722873277327659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37358651911710648291495029 3502373616722873277327659)
      ·
        refine ⟨5253560425084309915991489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502373616722873277327659 5253560425084309915991489)
        ·
          refine ⟨3940170318813232436993617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253560425084309915991489 3940170318813232436993617)
          ·
            refine ⟨2955127739109924327745213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3940170318813232436993617 2955127739109924327745213)
            ·
              refine ⟨1108172902166221622904455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2955127739109924327745213 1108172902166221622904455)
              ·
                refine ⟨1662259353249332434356683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108172902166221622904455 1662259353249332434356683)
                ·
                  refine ⟨2493389029873998651535025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662259353249332434356683 2493389029873998651535025)
                  ·
                    refine ⟨1870041772405498988651269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493389029873998651535025 1870041772405498988651269)
                    ·
                      refine ⟨350632832326031060372113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1870041772405498988651269 350632832326031060372113)
                      ·
                        rfl

theorem cell23_682855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_682855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682855 prefixEnd_682855 := by exact prefixLift 682855
  have htrace : WordTrace (prefixWord ++ tailWord_682855) baseStart_682855 baseEnd_682855 := by
    simpa [prefixWord, tailWord_682855, baseEnd_682855] using wordTrace_append hprefix tailTrace_682855
  have hstable : (prefixWord ++ tailWord_682855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682855).length < 2 ^ (prefixWord ++ tailWord_682855).sum := by decide
  have hdescent : baseEnd_682855 < baseStart_682855 := by decide
  rcases family_descends (prefixWord ++ tailWord_682855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682865 : List Nat := [1, 2, 2, 2, 1, 6, 2, 7]
def baseStart_682865 : Nat := 118140960795 + 682865 * 2 ^ 59
def prefixEnd_682865 : Nat := 4983230072969 + 3 ^ 40 * 682865 * 2
def baseEnd_682865 : Nat := 12986591375280593379521

theorem tailTrace_682865 : CollatzResearch.WordTrace tailWord_682865 prefixEnd_682865 12986591375280593379521 := by
  unfold tailWord_682865
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906132671104203902194049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16604088447402802601462699 24906132671104203902194049)
  ·
    refine ⟨18679599503328152926645537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24906132671104203902194049 18679599503328152926645537)
    ·
      refine ⟨14009699627496114694984153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18679599503328152926645537 14009699627496114694984153)
      ·
        refine ⟨10507274720622086021238115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14009699627496114694984153 10507274720622086021238115)
        ·
          refine ⟨15760912080933129031857173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10507274720622086021238115 15760912080933129031857173)
          ·
            refine ⟨738792753793740423368305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15760912080933129031857173 738792753793740423368305)
            ·
              refine ⟨554094565345305317526229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738792753793740423368305 554094565345305317526229)
              ·
                refine ⟨12986591375280593379521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 554094565345305317526229 12986591375280593379521)
                ·
                  rfl

theorem cell23_682865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 7].length) (baseStart_682865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682865 prefixEnd_682865 := by exact prefixLift 682865
  have htrace : WordTrace (prefixWord ++ tailWord_682865) baseStart_682865 baseEnd_682865 := by
    simpa [prefixWord, tailWord_682865, baseEnd_682865] using wordTrace_append hprefix tailTrace_682865
  have hstable : (prefixWord ++ tailWord_682865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682865).length < 2 ^ (prefixWord ++ tailWord_682865).sum := by decide
  have hdescent : baseEnd_682865 < baseStart_682865 := by decide
  rcases family_descends (prefixWord ++ tailWord_682865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682875 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 3]
def baseStart_682875 : Nat := 118140960795 + 682875 * 2 ^ 59
def prefixEnd_682875 : Nat := 4983230072969 + 3 ^ 40 * 682875 * 2
def baseEnd_682875 : Nat := 350643101939120982122021

theorem tailTrace_682875 : CollatzResearch.WordTrace tailWord_682875 prefixEnd_682875 350643101939120982122021 := by
  unfold tailWord_682875
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906497401067975610058079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16604331600711983740038719 24906497401067975610058079)
  ·
    refine ⟨37359746101601963415087119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24906497401067975610058079 37359746101601963415087119)
    ·
      refine ⟨56039619152402945122630679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37359746101601963415087119 56039619152402945122630679)
      ·
        refine ⟨84059428728604417683946019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56039619152402945122630679 84059428728604417683946019)
        ·
          refine ⟨126089143092906626525919029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84059428728604417683946019 126089143092906626525919029)
          ·
            refine ⟨11820857164959996236804909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126089143092906626525919029 11820857164959996236804909)
            ·
              refine ⟨4432821436859998588801841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11820857164959996236804909 4432821436859998588801841)
              ·
                refine ⟨3324616077644998941601381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432821436859998588801841 3324616077644998941601381)
                ·
                  refine ⟨623365514558437301550259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3324616077644998941601381 623365514558437301550259)
                  ·
                    refine ⟨935048271837655952325389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623365514558437301550259 935048271837655952325389)
                    ·
                      refine ⟨350643101939120982122021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 935048271837655952325389 350643101939120982122021)
                      ·
                        rfl

theorem cell23_682875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 3].length) (baseStart_682875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682875 prefixEnd_682875 := by exact prefixLift 682875
  have htrace : WordTrace (prefixWord ++ tailWord_682875) baseStart_682875 baseEnd_682875 := by
    simpa [prefixWord, tailWord_682875, baseEnd_682875] using wordTrace_append hprefix tailTrace_682875
  have hstable : (prefixWord ++ tailWord_682875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682875).length < 2 ^ (prefixWord ++ tailWord_682875).sum := by decide
  have hdescent : baseEnd_682875 < baseStart_682875 := by decide
  rcases family_descends (prefixWord ++ tailWord_682875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682919 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_682919 : Nat := 118140960795 + 682919 * 2 ^ 59
def prefixEnd_682919 : Nat := 4983230072969 + 3 ^ 40 * 682919 * 2
def baseEnd_682919 : Nat := 350665695087918809971819

theorem tailTrace_682919 : CollatzResearch.WordTrace tailWord_682919 prefixEnd_682919 350665695087918809971819 := by
  unfold tailWord_682919
  simp only [CollatzResearch.WordTrace]
  refine ⟨24908102212908571124659811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16605401475272380749773207 24908102212908571124659811)
  ·
    refine ⟨37362153319362856686989717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24908102212908571124659811 37362153319362856686989717)
    ·
      refine ⟨1751350936845133907202643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37362153319362856686989717 1751350936845133907202643)
      ·
        refine ⟨2627026405267700860803965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751350936845133907202643 2627026405267700860803965)
        ·
          refine ⟨985134901975387822801487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2627026405267700860803965 985134901975387822801487)
          ·
            refine ⟨1477702352963081734202231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985134901975387822801487 1477702352963081734202231)
            ·
              refine ⟨2216553529444622601303347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477702352963081734202231 2216553529444622601303347)
              ·
                refine ⟨3324830294166933901955021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216553529444622601303347 3324830294166933901955021)
                ·
                  refine ⟨1246811360312600213233133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3324830294166933901955021 1246811360312600213233133)
                  ·
                    refine ⟨467554260117225079962425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246811360312600213233133 467554260117225079962425)
                    ·
                      refine ⟨350665695087918809971819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467554260117225079962425 350665695087918809971819)
                      ·
                        rfl

theorem cell23_682919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_682919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682919 prefixEnd_682919 := by exact prefixLift 682919
  have htrace : WordTrace (prefixWord ++ tailWord_682919) baseStart_682919 baseEnd_682919 := by
    simpa [prefixWord, tailWord_682919, baseEnd_682919] using wordTrace_append hprefix tailTrace_682919
  have hstable : (prefixWord ++ tailWord_682919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682919).length < 2 ^ (prefixWord ++ tailWord_682919).sum := by decide
  have hdescent : baseEnd_682919 < baseStart_682919 := by decide
  rcases family_descends (prefixWord ++ tailWord_682919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682962 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_682962 : Nat := 118140960795 + 682962 * 2 ^ 59
def prefixEnd_682962 : Nat := 4983230072969 + 3 ^ 40 * 682962 * 2
def baseEnd_682962 : Nat := 350687774756062141734121

theorem tailTrace_682962 : CollatzResearch.WordTrace tailWord_682962 prefixEnd_682962 350687774756062141734121 := by
  unfold tailWord_682962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227417637938197367118785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16606447034501859645650093 6227417637938197367118785)
  ·
    refine ⟨4670563228453648025339089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6227417637938197367118785 4670563228453648025339089)
    ·
      refine ⟨3502922421340236019004317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4670563228453648025339089 3502922421340236019004317)
      ·
        refine ⟨1313595908002588507126619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3502922421340236019004317 1313595908002588507126619)
        ·
          refine ⟨1970393862003882760689929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313595908002588507126619 1970393862003882760689929)
          ·
            refine ⟨1477795396502912070517447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970393862003882760689929 1477795396502912070517447)
            ·
              refine ⟨2216693094754368105776171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477795396502912070517447 2216693094754368105776171)
              ·
                refine ⟨3325039642131552158664257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216693094754368105776171 3325039642131552158664257)
                ·
                  refine ⟨2493779731598664118998193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3325039642131552158664257 2493779731598664118998193)
                  ·
                    refine ⟨1870334798698998089248645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493779731598664118998193 1870334798698998089248645)
                    ·
                      refine ⟨350687774756062141734121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1870334798698998089248645 350687774756062141734121)
                      ·
                        rfl

theorem cell23_682962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_682962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682962 prefixEnd_682962 := by exact prefixLift 682962
  have htrace : WordTrace (prefixWord ++ tailWord_682962) baseStart_682962 baseEnd_682962 := by
    simpa [prefixWord, tailWord_682962, baseEnd_682962] using wordTrace_append hprefix tailTrace_682962
  have hstable : (prefixWord ++ tailWord_682962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682962).length < 2 ^ (prefixWord ++ tailWord_682962).sum := by decide
  have hdescent : baseEnd_682962 < baseStart_682962 := by decide
  rcases family_descends (prefixWord ++ tailWord_682962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682966 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_682966 : Nat := 118140960795 + 682966 * 2 ^ 59
def prefixEnd_682966 : Nat := 4983230072969 + 3 ^ 40 * 682966 * 2
def baseEnd_682966 : Nat := 350689828678680126084103

theorem tailTrace_682966 : CollatzResearch.WordTrace tailWord_682966 prefixEnd_682966 350689828678680126084103 := by
  unfold tailWord_682966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556863527733643634476297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16606544295825532101080501 1556863527733643634476297)
  ·
    refine ⟨1167647645800232725857223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1556863527733643634476297 1167647645800232725857223)
    ·
      refine ⟨1751471468700349088785835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167647645800232725857223 1751471468700349088785835)
      ·
        refine ⟨2627207203050523633178753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751471468700349088785835 2627207203050523633178753)
        ·
          refine ⟨1970405402287892724884065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627207203050523633178753 1970405402287892724884065)
          ·
            refine ⟨1477804051715919543663049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970405402287892724884065 1477804051715919543663049)
            ·
              refine ⟨1108353038786939657747287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477804051715919543663049 1108353038786939657747287)
              ·
                refine ⟨1662529558180409486620931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108353038786939657747287 1662529558180409486620931)
                ·
                  refine ⟨2493794337270614229931397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662529558180409486620931 2493794337270614229931397)
                  ·
                    refine ⟨467586438238240168112137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493794337270614229931397 467586438238240168112137)
                    ·
                      refine ⟨350689828678680126084103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467586438238240168112137 350689828678680126084103)
                      ·
                        rfl

theorem cell23_682966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_682966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_682966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_682966 prefixEnd_682966 := by exact prefixLift 682966
  have htrace : WordTrace (prefixWord ++ tailWord_682966) baseStart_682966 baseEnd_682966 := by
    simpa [prefixWord, tailWord_682966, baseEnd_682966] using wordTrace_append hprefix tailTrace_682966
  have hstable : (prefixWord ++ tailWord_682966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682966).length < 2 ^ (prefixWord ++ tailWord_682966).sum := by decide
  have hdescent : baseEnd_682966 < baseStart_682966 := by decide
  rcases family_descends (prefixWord ++ tailWord_682966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683005 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_683005 : Nat := 118140960795 + 683005 * 2 ^ 59
def prefixEnd_683005 : Nat := 4983230072969 + 3 ^ 40 * 683005 * 2
def baseEnd_683005 : Nat := 350709854424205473496423

theorem tailTrace_683005 : CollatzResearch.WordTrace tailWord_683005 prefixEnd_683005 350709854424205473496423 := by
  unfold tailWord_683005
  simp only [CollatzResearch.WordTrace]
  refine ⟨24911238890597007812290469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16607492593731338541526979 24911238890597007812290469)
  ·
    refine ⟨4670857291986938964804463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24911238890597007812290469 4670857291986938964804463)
    ·
      refine ⟨7006285937980408447206695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670857291986938964804463 7006285937980408447206695)
      ·
        refine ⟨10509428906970612670810043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7006285937980408447206695 10509428906970612670810043)
        ·
          refine ⟨15764143360455919006215065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10509428906970612670810043 15764143360455919006215065)
          ·
            refine ⟨11823107520341939254661299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15764143360455919006215065 11823107520341939254661299)
            ·
              refine ⟨17734661280512908881991949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11823107520341939254661299 17734661280512908881991949)
              ·
                refine ⟨6650497980192340830746981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17734661280512908881991949 6650497980192340830746981)
                ·
                  refine ⟨1246968371286063905765059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6650497980192340830746981 1246968371286063905765059)
                  ·
                    refine ⟨1870452556929095858647589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246968371286063905765059 1870452556929095858647589)
                    ·
                      refine ⟨350709854424205473496423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1870452556929095858647589 350709854424205473496423)
                      ·
                        rfl

theorem cell23_683005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_683005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683005 prefixEnd_683005 := by exact prefixLift 683005
  have htrace : WordTrace (prefixWord ++ tailWord_683005) baseStart_683005 baseEnd_683005 := by
    simpa [prefixWord, tailWord_683005, baseEnd_683005] using wordTrace_append hprefix tailTrace_683005
  have hstable : (prefixWord ++ tailWord_683005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683005).length < 2 ^ (prefixWord ++ tailWord_683005).sum := by decide
  have hdescent : baseEnd_683005 < baseStart_683005 := by decide
  rcases family_descends (prefixWord ++ tailWord_683005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683032 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_683032 : Nat := 118140960795 + 683032 * 2 ^ 59
def prefixEnd_683032 : Nat := 4983230072969 + 3 ^ 40 * 683032 * 2
def baseEnd_683032 : Nat := 116907906133958955952933

theorem tailTrace_683032 : CollatzResearch.WordTrace tailWord_683032 prefixEnd_683032 116907906133958955952933 := by
  unfold tailWord_683032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456111830749595711761675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16608149107666127615682233 12456111830749595711761675)
  ·
    refine ⟨18684167746124393567642513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12456111830749595711761675 18684167746124393567642513)
    ·
      refine ⟨14013125809593295175731885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18684167746124393567642513 14013125809593295175731885)
      ·
        refine ⟨5254922178597485690899457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14013125809593295175731885 5254922178597485690899457)
        ·
          refine ⟨3941191633948114268174593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5254922178597485690899457 3941191633948114268174593)
          ·
            refine ⟨2955893725461085701130945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3941191633948114268174593 2955893725461085701130945)
            ·
              refine ⟨2216920294095814275848209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955893725461085701130945 2216920294095814275848209)
              ·
                refine ⟨1662690220571860706886157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216920294095814275848209 1662690220571860706886157)
                ·
                  refine ⟨623508832714447765082309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662690220571860706886157 623508832714447765082309)
                  ·
                    refine ⟨116907906133958955952933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623508832714447765082309 116907906133958955952933)
                    ·
                      rfl

theorem cell23_683032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_683032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683032 prefixEnd_683032 := by exact prefixLift 683032
  have htrace : WordTrace (prefixWord ++ tailWord_683032) baseStart_683032 baseEnd_683032 := by
    simpa [prefixWord, tailWord_683032, baseEnd_683032] using wordTrace_append hprefix tailTrace_683032
  have hstable : (prefixWord ++ tailWord_683032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683032).length < 2 ^ (prefixWord ++ tailWord_683032).sum := by decide
  have hdescent : baseEnd_683032 < baseStart_683032 := by decide
  rcases family_descends (prefixWord ++ tailWord_683032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683042 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_683042 : Nat := 118140960795 + 683042 * 2 ^ 59
def prefixEnd_683042 : Nat := 4983230072969 + 3 ^ 40 * 683042 * 2
def baseEnd_683042 : Nat := 350728853208421828733753

theorem tailTrace_683042 : CollatzResearch.WordTrace tailWord_683042 prefixEnd_683042 350728853208421828733753 := by
  unfold tailWord_683042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228147097865740782846845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16608392260975308754258253 6228147097865740782846845)
  ·
    refine ⟨2335555161699652793567567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6228147097865740782846845 2335555161699652793567567)
    ·
      refine ⟨3503332742549479190351351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335555161699652793567567 3503332742549479190351351)
      ·
        refine ⟨5254999113824218785527027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503332742549479190351351 5254999113824218785527027)
        ·
          refine ⟨7882498670736328178290541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5254999113824218785527027 7882498670736328178290541)
          ·
            refine ⟨2955937001526123066858953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7882498670736328178290541 2955937001526123066858953)
            ·
              refine ⟨2216952751144592300144215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955937001526123066858953 2216952751144592300144215)
              ·
                refine ⟨3325429126716888450216323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216952751144592300144215 3325429126716888450216323)
                ·
                  refine ⟨4988143690075332675324485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325429126716888450216323 4988143690075332675324485)
                  ·
                    refine ⟨935276941889124876623341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988143690075332675324485 935276941889124876623341)
                    ·
                      refine ⟨350728853208421828733753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 935276941889124876623341 350728853208421828733753)
                      ·
                        rfl

theorem cell23_683042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_683042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683042 prefixEnd_683042 := by exact prefixLift 683042
  have htrace : WordTrace (prefixWord ++ tailWord_683042) baseStart_683042 baseEnd_683042 := by
    simpa [prefixWord, tailWord_683042, baseEnd_683042] using wordTrace_append hprefix tailTrace_683042
  have hstable : (prefixWord ++ tailWord_683042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683042).length < 2 ^ (prefixWord ++ tailWord_683042).sum := by decide
  have hdescent : baseEnd_683042 < baseStart_683042 := by decide
  rcases family_descends (prefixWord ++ tailWord_683042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683062 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_683062 : Nat := 118140960795 + 683062 * 2 ^ 59
def prefixEnd_683062 : Nat := 4983230072969 + 3 ^ 40 * 683062 * 2
def baseEnd_683062 : Nat := 38971013646834638942629

theorem tailTrace_683062 : CollatzResearch.WordTrace tailWord_683062 prefixEnd_683062 38971013646834638942629 := by
  unfold tailWord_683062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557082365711906659194715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16608878567593671031410293 1557082365711906659194715)
  ·
    refine ⟨2335623548567859988792073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1557082365711906659194715 2335623548567859988792073)
    ·
      refine ⟨1751717661425894991594055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2335623548567859988792073 1751717661425894991594055)
      ·
        refine ⟨2627576492138842487391083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751717661425894991594055 2627576492138842487391083)
        ·
          refine ⟨3941364738208263731086625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627576492138842487391083 3941364738208263731086625)
          ·
            refine ⟨2956023553656197798314969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3941364738208263731086625 2956023553656197798314969)
            ·
              refine ⟨2217017665242148348736227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956023553656197798314969 2217017665242148348736227)
              ·
                refine ⟨3325526497863222523104341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217017665242148348736227 3325526497863222523104341)
                ·
                  refine ⟨38971013646834638942629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3325526497863222523104341 38971013646834638942629)
                  ·
                    rfl

theorem cell23_683062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_683062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683062 prefixEnd_683062 := by exact prefixLift 683062
  have htrace : WordTrace (prefixWord ++ tailWord_683062) baseStart_683062 baseEnd_683062 := by
    simpa [prefixWord, tailWord_683062, baseEnd_683062] using wordTrace_append hprefix tailTrace_683062
  have hstable : (prefixWord ++ tailWord_683062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683062).length < 2 ^ (prefixWord ++ tailWord_683062).sum := by decide
  have hdescent : baseEnd_683062 < baseStart_683062 := by decide
  rcases family_descends (prefixWord ++ tailWord_683062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683075 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 3, 5]
def baseStart_683075 : Nat := 118140960795 + 683075 * 2 ^ 59
def prefixEnd_683075 : Nat := 4983230072969 + 3 ^ 40 * 683075 * 2
def baseEnd_683075 : Nat := 116915266023340066540367

theorem tailTrace_683075 : CollatzResearch.WordTrace tailWord_683075 prefixEnd_683075 116915266023340066540367 := by
  unfold tailWord_683075
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913792000343409767338679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16609194666895606511559119 24913792000343409767338679)
  ·
    refine ⟨37370688000515114651008019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24913792000343409767338679 37370688000515114651008019)
    ·
      refine ⟨56056032000772671976512029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37370688000515114651008019 56056032000772671976512029)
      ·
        refine ⟨21021012000289751991192011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56056032000772671976512029 21021012000289751991192011)
        ·
          refine ⟨31531518000434627986788017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21021012000289751991192011 31531518000434627986788017)
          ·
            refine ⟨23648638500325970990091013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31531518000434627986788017 23648638500325970990091013)
            ·
              refine ⟨4434119718811119560642065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23648638500325970990091013 4434119718811119560642065)
              ·
                refine ⟨3325589789108339670481549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434119718811119560642065 3325589789108339670481549)
                ·
                  refine ⟨1247096170915627376430581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3325589789108339670481549 1247096170915627376430581)
                  ·
                    refine ⟨116915266023340066540367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1247096170915627376430581 116915266023340066540367)
                    ·
                      rfl

theorem cell23_683075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 5].length) (baseStart_683075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683075 prefixEnd_683075 := by exact prefixLift 683075
  have htrace : WordTrace (prefixWord ++ tailWord_683075) baseStart_683075 baseEnd_683075 := by
    simpa [prefixWord, tailWord_683075, baseEnd_683075] using wordTrace_append hprefix tailTrace_683075
  have hstable : (prefixWord ++ tailWord_683075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683075).length < 2 ^ (prefixWord ++ tailWord_683075).sum := by decide
  have hdescent : baseEnd_683075 < baseStart_683075 := by decide
  rcases family_descends (prefixWord ++ tailWord_683075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683079 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 6]
def baseStart_683079 : Nat := 118140960795 + 683079 * 2 ^ 59
def prefixEnd_683079 : Nat := 4983230072969 + 3 ^ 40 * 683079 * 2
def baseEnd_683079 : Nat := 38971983554737575996787

theorem tailTrace_683079 : CollatzResearch.WordTrace tailWord_683079 prefixEnd_683079 38971983554737575996787 := by
  unfold tailWord_683079
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913937892328918450484291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16609291928219278966989527 24913937892328918450484291)
  ·
    refine ⟨37370906838493377675726437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24913937892328918450484291 37370906838493377675726437)
    ·
      refine ⟨7007045032217508314198707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37370906838493377675726437 7007045032217508314198707)
      ·
        refine ⟨10510567548326262471298061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007045032217508314198707 10510567548326262471298061)
        ·
          refine ⟨3941462830622348426736773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10510567548326262471298061 3941462830622348426736773)
          ·
            refine ⟨739024280741690330013145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3941462830622348426736773 739024280741690330013145)
            ·
              refine ⟨554268210556267747509859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739024280741690330013145 554268210556267747509859)
              ·
                refine ⟨831402315834401621264789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554268210556267747509859 831402315834401621264789)
                ·
                  refine ⟨38971983554737575996787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 831402315834401621264789 38971983554737575996787)
                  ·
                    rfl

theorem cell23_683079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 6].length) (baseStart_683079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683079 prefixEnd_683079 := by exact prefixLift 683079
  have htrace : WordTrace (prefixWord ++ tailWord_683079) baseStart_683079 baseEnd_683079 := by
    simpa [prefixWord, tailWord_683079, baseEnd_683079] using wordTrace_append hprefix tailTrace_683079
  have hstable : (prefixWord ++ tailWord_683079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683079).length < 2 ^ (prefixWord ++ tailWord_683079).sum := by decide
  have hdescent : baseEnd_683079 < baseStart_683079 := by decide
  rcases family_descends (prefixWord ++ tailWord_683079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683082 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_683082 : Nat := 118140960795 + 683082 * 2 ^ 59
def prefixEnd_683082 : Nat := 4983230072969 + 3 ^ 40 * 683082 * 2
def baseEnd_683082 : Nat := 350749392434601672233569

theorem tailTrace_683082 : CollatzResearch.WordTrace tailWord_683082 prefixEnd_683082 350749392434601672233569 := by
  unfold tailWord_683082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228511827829512490710875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16609364874212033308562333 6228511827829512490710875)
  ·
    refine ⟨9342767741744268736066313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6228511827829512490710875 9342767741744268736066313)
    ·
      refine ⟨7007075806308201552049735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9342767741744268736066313 7007075806308201552049735)
      ·
        refine ⟨10510613709462302328074603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007075806308201552049735 10510613709462302328074603)
        ·
          refine ⟨15765920564193453492111905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510613709462302328074603 15765920564193453492111905)
          ·
            refine ⟨11824440423145090119083929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15765920564193453492111905 11824440423145090119083929)
            ·
              refine ⟨8868330317358817589312947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11824440423145090119083929 8868330317358817589312947)
              ·
                refine ⟨13302495476038226383969421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868330317358817589312947 13302495476038226383969421)
                ·
                  refine ⟨4988435803514334893988533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13302495476038226383969421 4988435803514334893988533)
                  ·
                    refine ⟨467665856579468896311425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4988435803514334893988533 467665856579468896311425)
                    ·
                      refine ⟨350749392434601672233569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467665856579468896311425 350749392434601672233569)
                      ·
                        rfl

theorem cell23_683082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_683082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683082 prefixEnd_683082 := by exact prefixLift 683082
  have htrace : WordTrace (prefixWord ++ tailWord_683082) baseStart_683082 baseEnd_683082 := by
    simpa [prefixWord, tailWord_683082, baseEnd_683082] using wordTrace_append hprefix tailTrace_683082
  have hstable : (prefixWord ++ tailWord_683082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683082).length < 2 ^ (prefixWord ++ tailWord_683082).sum := by decide
  have hdescent : baseEnd_683082 < baseStart_683082 := by decide
  rcases family_descends (prefixWord ++ tailWord_683082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683105 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_683105 : Nat := 118140960795 + 683105 * 2 ^ 59
def prefixEnd_683105 : Nat := 4983230072969 + 3 ^ 40 * 683105 * 2
def baseEnd_683105 : Nat := 116920400829885027415321

theorem tailTrace_683105 : CollatzResearch.WordTrace tailWord_683105 prefixEnd_683105 116920400829885027415321 := by
  unfold tailWord_683105
  simp only [CollatzResearch.WordTrace]
  refine ⟨24914886190234724890930769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16609924126823149927287179 24914886190234724890930769)
  ·
    refine ⟨18686164642676043668198077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24914886190234724890930769 18686164642676043668198077)
    ·
      refine ⟨7007311741003516375574279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18686164642676043668198077 7007311741003516375574279)
      ·
        refine ⟨10510967611505274563361419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007311741003516375574279 10510967611505274563361419)
        ·
          refine ⟨15766451417257911845042129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510967611505274563361419 15766451417257911845042129)
          ·
            refine ⟨11824838562943433883781597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15766451417257911845042129 11824838562943433883781597)
            ·
              refine ⟨4434314461103787706418099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11824838562943433883781597 4434314461103787706418099)
              ·
                refine ⟨6651471691655681559627149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434314461103787706418099 6651471691655681559627149)
                ·
                  refine ⟨2494301884370880584860181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6651471691655681559627149 2494301884370880584860181)
                  ·
                    refine ⟨116920400829885027415321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2494301884370880584860181 116920400829885027415321)
                    ·
                      rfl

theorem cell23_683105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_683105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683105 prefixEnd_683105 := by exact prefixLift 683105
  have htrace : WordTrace (prefixWord ++ tailWord_683105) baseStart_683105 baseEnd_683105 := by
    simpa [prefixWord, tailWord_683105, baseEnd_683105] using wordTrace_append hprefix tailTrace_683105
  have hstable : (prefixWord ++ tailWord_683105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683105).length < 2 ^ (prefixWord ++ tailWord_683105).sum := by decide
  have hdescent : baseEnd_683105 < baseStart_683105 := by decide
  rcases family_descends (prefixWord ++ tailWord_683105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683109 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_683109 : Nat := 118140960795 + 683109 * 2 ^ 59
def prefixEnd_683109 : Nat := 4983230072969 + 3 ^ 40 * 683109 * 2
def baseEnd_683109 : Nat := 116921085470757688865315

theorem tailTrace_683109 : CollatzResearch.WordTrace tailWord_683109 prefixEnd_683109 116921085470757688865315 := by
  unfold tailWord_683109
  simp only [CollatzResearch.WordTrace]
  refine ⟨24915032082220233574076381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16610021388146822382717587 24915032082220233574076381)
  ·
    refine ⟨9343137030832587590278643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24915032082220233574076381 9343137030832587590278643)
    ·
      refine ⟨14014705546248881385417965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343137030832587590278643 14014705546248881385417965)
      ·
        refine ⟨5255514579843330519531737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14014705546248881385417965 5255514579843330519531737)
        ·
          refine ⟨3941635934882497889648803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5255514579843330519531737 3941635934882497889648803)
          ·
            refine ⟨5912453902323746834473205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941635934882497889648803 5912453902323746834473205)
            ·
              refine ⟨554292553342851265731863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5912453902323746834473205 554292553342851265731863)
              ·
                refine ⟨831438830014276898597795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554292553342851265731863 831438830014276898597795)
                ·
                  refine ⟨1247158245021415347896693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831438830014276898597795 1247158245021415347896693)
                  ·
                    refine ⟨116921085470757688865315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1247158245021415347896693 116921085470757688865315)
                    ·
                      rfl

theorem cell23_683109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_683109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683109 prefixEnd_683109 := by exact prefixLift 683109
  have htrace : WordTrace (prefixWord ++ tailWord_683109) baseStart_683109 baseEnd_683109 := by
    simpa [prefixWord, tailWord_683109, baseEnd_683109] using wordTrace_append hprefix tailTrace_683109
  have hstable : (prefixWord ++ tailWord_683109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683109).length < 2 ^ (prefixWord ++ tailWord_683109).sum := by decide
  have hdescent : baseEnd_683109 < baseStart_683109 := by decide
  rcases family_descends (prefixWord ++ tailWord_683109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683132 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_683132 : Nat := 118140960795 + 683132 * 2 ^ 59
def prefixEnd_683132 : Nat := 4983230072969 + 3 ^ 40 * 683132 * 2
def baseEnd_683132 : Nat := 350775066467326476608339

theorem tailTrace_683132 : CollatzResearch.WordTrace tailWord_683132 prefixEnd_683132 350775066467326476608339 := by
  unfold tailWord_683132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457935480568454251081825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16610580640757939001442433 12457935480568454251081825)
  ·
    refine ⟨9343451610426340688311369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12457935480568454251081825 9343451610426340688311369)
    ·
      refine ⟨7007588707819755516233527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9343451610426340688311369 7007588707819755516233527)
      ·
        refine ⟨10511383061729633274350291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007588707819755516233527 10511383061729633274350291)
        ·
          refine ⟨15767074592594449911525437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10511383061729633274350291 15767074592594449911525437)
          ·
            refine ⟨5912652972222918716822039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15767074592594449911525437 5912652972222918716822039)
            ·
              refine ⟨8868979458334378075233059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912652972222918716822039 8868979458334378075233059)
              ·
                refine ⟨13303469187501567112849589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868979458334378075233059 13303469187501567112849589)
                ·
                  refine ⟨1247200236328271916829649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13303469187501567112849589 1247200236328271916829649)
                  ·
                    refine ⟨935400177246203937622237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1247200236328271916829649 935400177246203937622237)
                    ·
                      refine ⟨350775066467326476608339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 935400177246203937622237 350775066467326476608339)
                      ·
                        rfl

theorem cell23_683132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_683132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683132 prefixEnd_683132 := by exact prefixLift 683132
  have htrace : WordTrace (prefixWord ++ tailWord_683132) baseStart_683132 baseEnd_683132 := by
    simpa [prefixWord, tailWord_683132, baseEnd_683132] using wordTrace_append hprefix tailTrace_683132
  have hstable : (prefixWord ++ tailWord_683132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683132).length < 2 ^ (prefixWord ++ tailWord_683132).sum := by decide
  have hdescent : baseEnd_683132 < baseStart_683132 := by decide
  rcases family_descends (prefixWord ++ tailWord_683132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683146 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_683146 : Nat := 118140960795 + 683146 * 2 ^ 59
def prefixEnd_683146 : Nat := 4983230072969 + 3 ^ 40 * 683146 * 2
def baseEnd_683146 : Nat := 350782255196489421833275

theorem tailTrace_683146 : CollatzResearch.WordTrace tailWord_683146 prefixEnd_683146 350782255196489421833275 := by
  unfold tailWord_683146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229095395771547223293323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16610921055390792595448861 6229095395771547223293323)
  ·
    refine ⟨9343643093657320834939985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6229095395771547223293323 9343643093657320834939985)
    ·
      refine ⟨7007732320242990626204989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9343643093657320834939985 7007732320242990626204989)
      ·
        refine ⟨2627899620091121484826871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7007732320242990626204989 2627899620091121484826871)
        ·
          refine ⟨3941849430136682227240307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627899620091121484826871 3941849430136682227240307)
          ·
            refine ⟨5912774145205023340860461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941849430136682227240307 5912774145205023340860461)
            ·
              refine ⟨2217290304451883752822673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5912774145205023340860461 2217290304451883752822673)
              ·
                refine ⟨1662967728338912814617005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217290304451883752822673 1662967728338912814617005)
                ·
                  refine ⟨623612898127092305481377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662967728338912814617005 623612898127092305481377)
                  ·
                    refine ⟨467709673595319229111033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623612898127092305481377 467709673595319229111033)
                    ·
                      refine ⟨350782255196489421833275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467709673595319229111033 350782255196489421833275)
                      ·
                        rfl

theorem cell23_683146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_683146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683146 prefixEnd_683146 := by exact prefixLift 683146
  have htrace : WordTrace (prefixWord ++ tailWord_683146) baseStart_683146 baseEnd_683146 := by
    simpa [prefixWord, tailWord_683146, baseEnd_683146] using wordTrace_append hprefix tailTrace_683146
  have hstable : (prefixWord ++ tailWord_683146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683146).length < 2 ^ (prefixWord ++ tailWord_683146).sum := by decide
  have hdescent : baseEnd_683146 < baseStart_683146 := by decide
  rcases family_descends (prefixWord ++ tailWord_683146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683190 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_683190 : Nat := 118140960795 + 683190 * 2 ^ 59
def prefixEnd_683190 : Nat := 4983230072969 + 3 ^ 40 * 683190 * 2
def baseEnd_683190 : Nat := 116934949448429083227691

theorem tailTrace_683190 : CollatzResearch.WordTrace tailWord_683190 prefixEnd_683190 116934949448429083227691 := by
  unfold tailWord_683190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557374149682924025485939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16611990929951189605183349 1557374149682924025485939)
  ·
    refine ⟨2336061224524386038228909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1557374149682924025485939 2336061224524386038228909)
    ·
      refine ⟨876022959196644764335841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2336061224524386038228909 876022959196644764335841)
      ·
        refine ⟨657017219397483573251881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 876022959196644764335841 657017219397483573251881)
        ·
          refine ⟨492762914548112679938911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657017219397483573251881 492762914548112679938911)
          ·
            refine ⟨739144371822169019908367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492762914548112679938911 739144371822169019908367)
            ·
              refine ⟨1108716557733253529862551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739144371822169019908367 1108716557733253529862551)
              ·
                refine ⟨1663074836599880294793827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108716557733253529862551 1663074836599880294793827)
                ·
                  refine ⟨2494612254899820442190741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663074836599880294793827 2494612254899820442190741)
                  ·
                    refine ⟨116934949448429083227691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2494612254899820442190741 116934949448429083227691)
                    ·
                      rfl

theorem cell23_683190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_683190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683190 prefixEnd_683190 := by exact prefixLift 683190
  have htrace : WordTrace (prefixWord ++ tailWord_683190) baseStart_683190 baseEnd_683190 := by
    simpa [prefixWord, tailWord_683190, baseEnd_683190] using wordTrace_append hprefix tailTrace_683190
  have hstable : (prefixWord ++ tailWord_683190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683190).length < 2 ^ (prefixWord ++ tailWord_683190).sum := by decide
  have hdescent : baseEnd_683190 < baseStart_683190 := by decide
  rcases family_descends (prefixWord ++ tailWord_683190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683195 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 8]
def baseStart_683195 : Nat := 118140960795 + 683195 * 2 ^ 59
def prefixEnd_683195 : Nat := 4983230072969 + 3 ^ 40 * 683195 * 2
def baseEnd_683195 : Nat := 116935805249519910040183

theorem tailTrace_683195 : CollatzResearch.WordTrace tailWord_683195 prefixEnd_683195 116935805249519910040183 := by
  unfold tailWord_683195
  simp only [CollatzResearch.WordTrace]
  refine ⟨24918168759908670261707039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16612112506605780174471359 24918168759908670261707039)
  ·
    refine ⟨37377253139863005392560559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24918168759908670261707039 37377253139863005392560559)
    ·
      refine ⟨56065879709794508088840839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37377253139863005392560559 56065879709794508088840839)
      ·
        refine ⟨84098819564691762133261259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56065879709794508088840839 84098819564691762133261259)
        ·
          refine ⟨126148229347037643199891889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84098819564691762133261259 126148229347037643199891889)
          ·
            refine ⟨94611172010278232399918917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126148229347037643199891889 94611172010278232399918917)
            ·
              refine ⟨17739594751927168574984797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94611172010278232399918917 17739594751927168574984797)
              ·
                refine ⟨6652348031972688215619299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17739594751927168574984797 6652348031972688215619299)
                ·
                  refine ⟨9978522047959032323428949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6652348031972688215619299 9978522047959032323428949)
                  ·
                    refine ⟨116935805249519910040183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9978522047959032323428949 116935805249519910040183)
                    ·
                      rfl

theorem cell23_683195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_683195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683195 prefixEnd_683195 := by exact prefixLift 683195
  have htrace : WordTrace (prefixWord ++ tailWord_683195) baseStart_683195 baseEnd_683195 := by
    simpa [prefixWord, tailWord_683195, baseEnd_683195] using wordTrace_append hprefix tailTrace_683195
  have hstable : (prefixWord ++ tailWord_683195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683195).length < 2 ^ (prefixWord ++ tailWord_683195).sum := by decide
  have hdescent : baseEnd_683195 < baseStart_683195 := by decide
  rcases family_descends (prefixWord ++ tailWord_683195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683196 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_683196 : Nat := 118140960795 + 683196 * 2 ^ 59
def prefixEnd_683196 : Nat := 4983230072969 + 3 ^ 40 * 683196 * 2
def baseEnd_683196 : Nat := 350807929229214226208045

theorem tailTrace_683196 : CollatzResearch.WordTrace tailWord_683196 prefixEnd_683196 350807929229214226208045 := by
  unfold tailWord_683196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459102616452523716246721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16612136821936698288328961 12459102616452523716246721)
  ·
    refine ⟨9344326962339392787185041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12459102616452523716246721 9344326962339392787185041)
    ·
      refine ⟨7008245221754544590388781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9344326962339392787185041 7008245221754544590388781)
      ·
        refine ⟨2628091958157954221395793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7008245221754544590388781 2628091958157954221395793)
        ·
          refine ⟨1971068968618465666046845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2628091958157954221395793 1971068968618465666046845)
          ·
            refine ⟨739150863231924624767567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1971068968618465666046845 739150863231924624767567)
            ·
              refine ⟨1108726294847886937151351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739150863231924624767567 1108726294847886937151351)
              ·
                refine ⟨1663089442271830405727027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108726294847886937151351 1663089442271830405727027)
                ·
                  refine ⟨2494634163407745608590541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663089442271830405727027 2494634163407745608590541)
                  ·
                    refine ⟨935487811277904603221453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2494634163407745608590541 935487811277904603221453)
                    ·
                      refine ⟨350807929229214226208045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 935487811277904603221453 350807929229214226208045)
                      ·
                        rfl

theorem cell23_683196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_683196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683196 prefixEnd_683196 := by exact prefixLift 683196
  have htrace : WordTrace (prefixWord ++ tailWord_683196) baseStart_683196 baseEnd_683196 := by
    simpa [prefixWord, tailWord_683196, baseEnd_683196] using wordTrace_append hprefix tailTrace_683196
  have hstable : (prefixWord ++ tailWord_683196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683196).length < 2 ^ (prefixWord ++ tailWord_683196).sum := by decide
  have hdescent : baseEnd_683196 < baseStart_683196 := by decide
  rcases family_descends (prefixWord ++ tailWord_683196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683236 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_683236 : Nat := 118140960795 + 683236 * 2 ^ 59
def prefixEnd_683236 : Nat := 4983230072969 + 3 ^ 40 * 683236 * 2
def baseEnd_683236 : Nat := 350828468455394069707861

theorem tailTrace_683236 : CollatzResearch.WordTrace tailWord_683236 prefixEnd_683236 350828468455394069707861 := by
  unfold tailWord_683236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459832076380067131974781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16613109435173422842633041 12459832076380067131974781)
  ·
    refine ⟨4672437028642525174490543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12459832076380067131974781 4672437028642525174490543)
    ·
      refine ⟨7008655542963787761735815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4672437028642525174490543 7008655542963787761735815)
      ·
        refine ⟨10512983314445681642603723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7008655542963787761735815 10512983314445681642603723)
        ·
          refine ⟨15769474971668522463905585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10512983314445681642603723 15769474971668522463905585)
          ·
            refine ⟨11827106228751391847929189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15769474971668522463905585 11827106228751391847929189)
            ·
              refine ⟨2217582417890885971486723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11827106228751391847929189 2217582417890885971486723)
              ·
                refine ⟨3326373626836328957230085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217582417890885971486723 3326373626836328957230085)
                ·
                  refine ⟨623695055031811679480641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3326373626836328957230085 623695055031811679480641)
                  ·
                    refine ⟨467771291273858759610481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623695055031811679480641 467771291273858759610481)
                    ·
                      refine ⟨350828468455394069707861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467771291273858759610481 350828468455394069707861)
                      ·
                        rfl

theorem cell23_683236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_683236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683236 prefixEnd_683236 := by exact prefixLift 683236
  have htrace : WordTrace (prefixWord ++ tailWord_683236) baseStart_683236 baseEnd_683236 := by
    simpa [prefixWord, tailWord_683236, baseEnd_683236] using wordTrace_append hprefix tailTrace_683236
  have hstable : (prefixWord ++ tailWord_683236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683236).length < 2 ^ (prefixWord ++ tailWord_683236).sum := by decide
  have hdescent : baseEnd_683236 < baseStart_683236 := by decide
  rcases family_descends (prefixWord ++ tailWord_683236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683293 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 5]
def baseStart_683293 : Nat := 118140960795 + 683293 * 2 ^ 59
def prefixEnd_683293 : Nat := 4983230072969 + 3 ^ 40 * 683293 * 2
def baseEnd_683293 : Nat := 38984192983633371855011

theorem tailTrace_683293 : CollatzResearch.WordTrace tailWord_683293 prefixEnd_683293 38984192983633371855011 := by
  unfold tailWord_683293
  simp only [CollatzResearch.WordTrace]
  refine ⟨24921743113553632998774533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16614495409035755332516355 24921743113553632998774533)
  ·
    refine ⟨4672826833791306187270225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24921743113553632998774533 4672826833791306187270225)
    ·
      refine ⟨3504620125343479640452669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4672826833791306187270225 3504620125343479640452669)
      ·
        refine ⟨1314232547003804865169751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3504620125343479640452669 1314232547003804865169751)
        ·
          refine ⟨1971348820505707297754627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314232547003804865169751 1971348820505707297754627)
          ·
            refine ⟨2957023230758560946631941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971348820505707297754627 2957023230758560946631941)
            ·
              refine ⟨554441855767230177493489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2957023230758560946631941 554441855767230177493489)
              ·
                refine ⟨415831391825422633120117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554441855767230177493489 415831391825422633120117)
                ·
                  refine ⟨38984192983633371855011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415831391825422633120117 38984192983633371855011)
                  ·
                    rfl

theorem cell23_683293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_683293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683293 prefixEnd_683293 := by exact prefixLift 683293
  have htrace : WordTrace (prefixWord ++ tailWord_683293) baseStart_683293 baseEnd_683293 := by
    simpa [prefixWord, tailWord_683293, baseEnd_683293] using wordTrace_append hprefix tailTrace_683293
  have hstable : (prefixWord ++ tailWord_683293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683293).length < 2 ^ (prefixWord ++ tailWord_683293).sum := by decide
  have hdescent : baseEnd_683293 < baseStart_683293 := by decide
  rcases family_descends (prefixWord ++ tailWord_683293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683326 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_683326 : Nat := 118140960795 + 683326 * 2 ^ 59
def prefixEnd_683326 : Nat := 4983230072969 + 3 ^ 40 * 683326 * 2
def baseEnd_683326 : Nat := 350874681714298717582447

theorem tailTrace_683326 : CollatzResearch.WordTrace tailWord_683326 prefixEnd_683326 350874681714298717582447 := by
  unfold tailWord_683326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115368340304259954340729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16615297814956053089817221 3115368340304259954340729)
  ·
    refine ⟨2336526255228194965755547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3115368340304259954340729 2336526255228194965755547)
    ·
      refine ⟨3504789382842292448633321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2336526255228194965755547 3504789382842292448633321)
      ·
        refine ⟨2628592037131719336474991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3504789382842292448633321 2628592037131719336474991)
        ·
          refine ⟨3942888055697579004712487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628592037131719336474991 3942888055697579004712487)
          ·
            refine ⟨5914332083546368507068731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942888055697579004712487 5914332083546368507068731)
            ·
              refine ⟨8871498125319552760603097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914332083546368507068731 8871498125319552760603097)
              ·
                refine ⟨6653623593989664570452323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8871498125319552760603097 6653623593989664570452323)
                ·
                  refine ⟨9980435390984496855678485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653623593989664570452323 9980435390984496855678485)
                  ·
                    refine ⟨467832908952398290109929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9980435390984496855678485 467832908952398290109929)
                    ·
                      refine ⟨350874681714298717582447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467832908952398290109929 350874681714298717582447)
                      ·
                        rfl

theorem cell23_683326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_683326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683326 prefixEnd_683326 := by exact prefixLift 683326
  have htrace : WordTrace (prefixWord ++ tailWord_683326) baseStart_683326 baseEnd_683326 := by
    simpa [prefixWord, tailWord_683326, baseEnd_683326] using wordTrace_append hprefix tailTrace_683326
  have hstable : (prefixWord ++ tailWord_683326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683326).length < 2 ^ (prefixWord ++ tailWord_683326).sum := by decide
  have hdescent : baseEnd_683326 < baseStart_683326 := by decide
  rcases family_descends (prefixWord ++ tailWord_683326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683349 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 8]
def baseStart_683349 : Nat := 118140960795 + 683349 * 2 ^ 59
def prefixEnd_683349 : Nat := 4983230072969 + 3 ^ 40 * 683349 * 2
def baseEnd_683349 : Nat := 38987387974372458621649

theorem tailTrace_683349 : CollatzResearch.WordTrace tailWord_683349 prefixEnd_683349 38987387974372458621649 := by
  unfold tailWord_683349
  simp only [CollatzResearch.WordTrace]
  refine ⟨24923785601350754562813101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16615857067567169708542067 24923785601350754562813101)
  ·
    refine ⟨9346419600506532961054913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24923785601350754562813101 9346419600506532961054913)
    ·
      refine ⟨7009814700379899720791185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9346419600506532961054913 7009814700379899720791185)
      ·
        refine ⟨5257361025284924790593389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7009814700379899720791185 5257361025284924790593389)
        ·
          refine ⟨1971510384481846796472521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5257361025284924790593389 1971510384481846796472521)
          ·
            refine ⟨1478632788361385097354391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971510384481846796472521 1478632788361385097354391)
            ·
              refine ⟨2217949182542077646031587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478632788361385097354391 2217949182542077646031587)
              ·
                refine ⟨3326923773813116469047381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217949182542077646031587 3326923773813116469047381)
                ·
                  refine ⟨38987387974372458621649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3326923773813116469047381 38987387974372458621649)
                  ·
                    rfl

theorem cell23_683349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_683349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683349 prefixEnd_683349 := by exact prefixLift 683349
  have htrace : WordTrace (prefixWord ++ tailWord_683349) baseStart_683349 baseEnd_683349 := by
    simpa [prefixWord, tailWord_683349, baseEnd_683349] using wordTrace_append hprefix tailTrace_683349
  have hstable : (prefixWord ++ tailWord_683349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683349).length < 2 ^ (prefixWord ++ tailWord_683349).sum := by decide
  have hdescent : baseEnd_683349 < baseStart_683349 := by decide
  rcases family_descends (prefixWord ++ tailWord_683349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683352 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_683352 : Nat := 118140960795 + 683352 * 2 ^ 59
def prefixEnd_683352 : Nat := 4983230072969 + 3 ^ 40 * 683352 * 2
def baseEnd_683352 : Nat := 350888032211315615857327

theorem tailTrace_683352 : CollatzResearch.WordTrace tailWord_683352 prefixEnd_683352 350888032211315615857327 := by
  unfold tailWord_683352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12461947510169943037586155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16615930013559924050114873 12461947510169943037586155)
  ·
    refine ⟨18692921265254914556379233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12461947510169943037586155 18692921265254914556379233)
    ·
      refine ⟨14019690948941185917284425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18692921265254914556379233 14019690948941185917284425)
      ·
        refine ⟨10514768211705889437963319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14019690948941185917284425 10514768211705889437963319)
        ·
          refine ⟨15772152317558834156944979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10514768211705889437963319 15772152317558834156944979)
          ·
            refine ⟨23658228476338251235417469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15772152317558834156944979 23658228476338251235417469)
            ·
              refine ⟨8871835678626844213281551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23658228476338251235417469 8871835678626844213281551)
              ·
                refine ⟨13307753517940266319922327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8871835678626844213281551 13307753517940266319922327)
                ·
                  refine ⟨19961630276910399479883491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13307753517940266319922327 19961630276910399479883491)
                  ·
                    refine ⟨29942445415365599219825237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19961630276910399479883491 29942445415365599219825237)
                    ·
                      refine ⟨350888032211315615857327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 29942445415365599219825237 350888032211315615857327)
                      ·
                        rfl

theorem cell23_683352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_683352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683352 prefixEnd_683352 := by exact prefixLift 683352
  have htrace : WordTrace (prefixWord ++ tailWord_683352) baseStart_683352 baseEnd_683352 := by
    simpa [prefixWord, tailWord_683352, baseEnd_683352] using wordTrace_append hprefix tailTrace_683352
  have hstable : (prefixWord ++ tailWord_683352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683352).length < 2 ^ (prefixWord ++ tailWord_683352).sum := by decide
  have hdescent : baseEnd_683352 < baseStart_683352 := by decide
  rcases family_descends (prefixWord ++ tailWord_683352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683376 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3]
def baseStart_683376 : Nat := 118140960795 + 683376 * 2 ^ 59
def prefixEnd_683376 : Nat := 4983230072969 + 3 ^ 40 * 683376 * 2
def baseEnd_683376 : Nat := 350900355747023521957217

theorem tailTrace_683376 : CollatzResearch.WordTrace tailWord_683376 prefixEnd_683376 350900355747023521957217 := by
  unfold tailWord_683376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462385186126469087022991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16616513581501958782697321 12462385186126469087022991)
  ·
    refine ⟨18693577779189703630534487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12462385186126469087022991 18693577779189703630534487)
    ·
      refine ⟨28040366668784555445801731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18693577779189703630534487 28040366668784555445801731)
      ·
        refine ⟨42060550003176833168702597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28040366668784555445801731 42060550003176833168702597)
        ·
          refine ⟨7886353125595656219131737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42060550003176833168702597 7886353125595656219131737)
          ·
            refine ⟨5914764844196742164348803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886353125595656219131737 5914764844196742164348803)
            ·
              refine ⟨8872147266295113246523205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914764844196742164348803 8872147266295113246523205)
              ·
                refine ⟨1663527612430333733723101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8872147266295113246523205 1663527612430333733723101)
                ·
                  refine ⟨623822854661375150146163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1663527612430333733723101 623822854661375150146163)
                  ·
                    refine ⟨935734281992062725219245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623822854661375150146163 935734281992062725219245)
                    ·
                      refine ⟨350900355747023521957217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 935734281992062725219245 350900355747023521957217)
                      ·
                        rfl

theorem cell23_683376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_683376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683376 prefixEnd_683376 := by exact prefixLift 683376
  have htrace : WordTrace (prefixWord ++ tailWord_683376) baseStart_683376 baseEnd_683376 := by
    simpa [prefixWord, tailWord_683376, baseEnd_683376] using wordTrace_append hprefix tailTrace_683376
  have hstable : (prefixWord ++ tailWord_683376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683376).length < 2 ^ (prefixWord ++ tailWord_683376).sum := by decide
  have hdescent : baseEnd_683376 < baseStart_683376 := by decide
  rcases family_descends (prefixWord ++ tailWord_683376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683396 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_683396 : Nat := 118140960795 + 683396 * 2 ^ 59
def prefixEnd_683396 : Nat := 4983230072969 + 3 ^ 40 * 683396 * 2
def baseEnd_683396 : Nat := 116970208453371147902375

theorem tailTrace_683396 : CollatzResearch.WordTrace tailWord_683396 prefixEnd_683396 116970208453371147902375 := by
  unfold tailWord_683396
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462749916090240794887021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16616999888120321059849361 12462749916090240794887021)
  ·
    refine ⟨4673531218533840298082633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12462749916090240794887021 4673531218533840298082633)
    ·
      refine ⟨3505148413900380223561975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673531218533840298082633 3505148413900380223561975)
      ·
        refine ⟨5257722620850570335342963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505148413900380223561975 5257722620850570335342963)
        ·
          refine ⟨7886583931275855503014445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257722620850570335342963 7886583931275855503014445)
          ·
            refine ⟨2957468974228445813630417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7886583931275855503014445 2957468974228445813630417)
            ·
              refine ⟨2218101730671334360222813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957468974228445813630417 2218101730671334360222813)
              ·
                refine ⟨831788149001750385083555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2218101730671334360222813 831788149001750385083555)
                ·
                  refine ⟨1247682223502625577625333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831788149001750385083555 1247682223502625577625333)
                  ·
                    refine ⟨116970208453371147902375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1247682223502625577625333 116970208453371147902375)
                    ·
                      rfl

theorem cell23_683396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_683396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683396 prefixEnd_683396 := by exact prefixLift 683396
  have htrace : WordTrace (prefixWord ++ tailWord_683396) baseStart_683396 baseEnd_683396 := by
    simpa [prefixWord, tailWord_683396, baseEnd_683396] using wordTrace_append hprefix tailTrace_683396
  have hstable : (prefixWord ++ tailWord_683396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683396).length < 2 ^ (prefixWord ++ tailWord_683396).sum := by decide
  have hdescent : baseEnd_683396 < baseStart_683396 := by decide
  rcases family_descends (prefixWord ++ tailWord_683396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683460 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_683460 : Nat := 118140960795 + 683460 * 2 ^ 59
def prefixEnd_683460 : Nat := 4983230072969 + 3 ^ 40 * 683460 * 2
def baseEnd_683460 : Nat := 116981162707333731102277

theorem tailTrace_683460 : CollatzResearch.WordTrace tailWord_683460 prefixEnd_683460 116981162707333731102277 := by
  unfold tailWord_683460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12463917051974310260051917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16618556069299080346735889 12463917051974310260051917)
  ·
    refine ⟨4673968894490366347519469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12463917051974310260051917 4673968894490366347519469)
    ·
      refine ⟨1752738335433887380319801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4673968894490366347519469 1752738335433887380319801)
      ·
        refine ⟨1314553751575415535239851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1752738335433887380319801 1314553751575415535239851)
        ·
          refine ⟨1971830627363123302859777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314553751575415535239851 1971830627363123302859777)
          ·
            refine ⟨1478872970522342477144833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971830627363123302859777 1478872970522342477144833)
            ·
              refine ⟨1109154727891756857858625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478872970522342477144833 1109154727891756857858625)
              ·
                refine ⟨831866045918817643393969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109154727891756857858625 831866045918817643393969)
                ·
                  refine ⟨623899534439113232545477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831866045918817643393969 623899534439113232545477)
                  ·
                    refine ⟨116981162707333731102277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623899534439113232545477 116981162707333731102277)
                    ·
                      rfl

theorem cell23_683460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_683460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683460 prefixEnd_683460 := by exact prefixLift 683460
  have htrace : WordTrace (prefixWord ++ tailWord_683460) baseStart_683460 baseEnd_683460 := by
    simpa [prefixWord, tailWord_683460, baseEnd_683460] using wordTrace_append hprefix tailTrace_683460
  have hstable : (prefixWord ++ tailWord_683460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683460).length < 2 ^ (prefixWord ++ tailWord_683460).sum := by decide
  have hdescent : baseEnd_683460 < baseStart_683460 := by decide
  rcases family_descends (prefixWord ++ tailWord_683460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683467 : List Nat := [1, 1, 1, 1, 3, 3, 6, 2, 1, 2, 2]
def baseStart_683467 : Nat := 118140960795 + 683467 * 2 ^ 59
def prefixEnd_683467 : Nat := 4983230072969 + 3 ^ 40 * 683467 * 2
def baseEnd_683467 : Nat := 350947082486582665919299

theorem tailTrace_683467 : CollatzResearch.WordTrace tailWord_683467 prefixEnd_683467 350947082486582665919299 := by
  unfold tailWord_683467
  simp only [CollatzResearch.WordTrace]
  refine ⟨24928089414923260715608655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16618726276615507143739103 24928089414923260715608655)
  ·
    refine ⟨37392134122384891073412983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24928089414923260715608655 37392134122384891073412983)
    ·
      refine ⟨56088201183577336610119475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37392134122384891073412983 56088201183577336610119475)
      ·
        refine ⟨84132301775366004915179213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56088201183577336610119475 84132301775366004915179213)
        ·
          refine ⟨31549613165762251843192205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84132301775366004915179213 31549613165762251843192205)
          ·
            refine ⟨11831104937160844441197077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31549613165762251843192205 11831104937160844441197077)
            ·
              refine ⟨554583043929414583181113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11831104937160844441197077 554583043929414583181113)
              ·
                refine ⟨415937282947060937385835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554583043929414583181113 415937282947060937385835)
                ·
                  refine ⟨623905924420591406078753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415937282947060937385835 623905924420591406078753)
                  ·
                    refine ⟨467929443315443554559065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623905924420591406078753 467929443315443554559065)
                    ·
                      refine ⟨350947082486582665919299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 467929443315443554559065 350947082486582665919299)
                      ·
                        rfl

theorem cell23_683467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 2, 2].length) (baseStart_683467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683467 prefixEnd_683467 := by exact prefixLift 683467
  have htrace : WordTrace (prefixWord ++ tailWord_683467) baseStart_683467 baseEnd_683467 := by
    simpa [prefixWord, tailWord_683467, baseEnd_683467] using wordTrace_append hprefix tailTrace_683467
  have hstable : (prefixWord ++ tailWord_683467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683467).length < 2 ^ (prefixWord ++ tailWord_683467).sum := by decide
  have hdescent : baseEnd_683467 < baseStart_683467 := by decide
  rcases family_descends (prefixWord ++ tailWord_683467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683576 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_683576 : Nat := 118140960795 + 683576 * 2 ^ 59
def prefixEnd_683576 : Nat := 4983230072969 + 3 ^ 40 * 683576 * 2
def baseEnd_683576 : Nat := 117001017292640913152099

theorem tailTrace_683576 : CollatzResearch.WordTrace tailWord_683576 prefixEnd_683576 117001017292640913152099 := by
  unfold tailWord_683576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466032485764186165663291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16621376647685581554217721 12466032485764186165663291)
  ·
    refine ⟨18699048728646279248494937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12466032485764186165663291 18699048728646279248494937)
    ·
      refine ⟨14024286546484709436371203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18699048728646279248494937 14024286546484709436371203)
      ·
        refine ⟨21036429819727064154556805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14024286546484709436371203 21036429819727064154556805)
        ·
          refine ⟨3944330591198824528979401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21036429819727064154556805 3944330591198824528979401)
          ·
            refine ⟨2958247943399118396734551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3944330591198824528979401 2958247943399118396734551)
            ·
              refine ⟨4437371915098677595101827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958247943399118396734551 4437371915098677595101827)
              ·
                refine ⟨6656057872648016392652741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437371915098677595101827 6656057872648016392652741)
                ·
                  refine ⟨1248010851121503073622389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6656057872648016392652741 1248010851121503073622389)
                  ·
                    refine ⟨117001017292640913152099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1248010851121503073622389 117001017292640913152099)
                    ·
                      rfl

theorem cell23_683576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_683576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683576 prefixEnd_683576 := by exact prefixLift 683576
  have htrace : WordTrace (prefixWord ++ tailWord_683576) baseStart_683576 baseEnd_683576 := by
    simpa [prefixWord, tailWord_683576, baseEnd_683576] using wordTrace_append hprefix tailTrace_683576
  have hstable : (prefixWord ++ tailWord_683576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683576).length < 2 ^ (prefixWord ++ tailWord_683576).sum := by decide
  have hdescent : baseEnd_683576 < baseStart_683576 := by decide
  rcases family_descends (prefixWord ++ tailWord_683576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683580 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 7]
def baseStart_683580 : Nat := 118140960795 + 683580 * 2 ^ 59
def prefixEnd_683580 : Nat := 4983230072969 + 3 ^ 40 * 683580 * 2
def baseEnd_683580 : Nat := 39000567311171191534031

theorem tailTrace_683580 : CollatzResearch.WordTrace tailWord_683580 prefixEnd_683580 39000567311171191534031 := by
  unfold tailWord_683580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466105431756940507236097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16621473909009254009648129 12466105431756940507236097)
  ·
    refine ⟨9349579073817705380427073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12466105431756940507236097 9349579073817705380427073)
    ·
      refine ⟨7012184305363279035320305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9349579073817705380427073 7012184305363279035320305)
      ·
        refine ⟨5259138229022459276490229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7012184305363279035320305 5259138229022459276490229)
        ·
          refine ⟨493044208970855557170959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5259138229022459276490229 493044208970855557170959)
          ·
            refine ⟨739566313456283335756439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493044208970855557170959 739566313456283335756439)
            ·
              refine ⟨1109349470184425003634659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739566313456283335756439 1109349470184425003634659)
              ·
                refine ⟨1664024205276637505451989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109349470184425003634659 1664024205276637505451989)
                ·
                  refine ⟨39000567311171191534031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1664024205276637505451989 39000567311171191534031)
                  ·
                    rfl

theorem cell23_683580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_683580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683580 prefixEnd_683580 := by exact prefixLift 683580
  have htrace : WordTrace (prefixWord ++ tailWord_683580) baseStart_683580 baseEnd_683580 := by
    simpa [prefixWord, tailWord_683580, baseEnd_683580] using wordTrace_append hprefix tailTrace_683580
  have hstable : (prefixWord ++ tailWord_683580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683580).length < 2 ^ (prefixWord ++ tailWord_683580).sum := by decide
  have hdescent : baseEnd_683580 < baseStart_683580 := by decide
  rcases family_descends (prefixWord ++ tailWord_683580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683591 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_683591 : Nat := 118140960795 + 683591 * 2 ^ 59
def prefixEnd_683591 : Nat := 4983230072969 + 3 ^ 40 * 683591 * 2
def baseEnd_683591 : Nat := 351010754087740180768729

theorem tailTrace_683591 : CollatzResearch.WordTrace tailWord_683591 prefixEnd_683591 351010754087740180768729 := by
  unfold tailWord_683591
  simp only [CollatzResearch.WordTrace]
  refine ⟨24932612066474029893122627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16621741377649353262081751 24932612066474029893122627)
  ·
    refine ⟨37398918099711044839683941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24932612066474029893122627 37398918099711044839683941)
    ·
      refine ⟨7012297143695820907440739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37398918099711044839683941 7012297143695820907440739)
      ·
        refine ⟨10518445715543731361161109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7012297143695820907440739 10518445715543731361161109)
        ·
          refine ⟨493052142916112407554427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10518445715543731361161109 493052142916112407554427)
          ·
            refine ⟨739578214374168611331641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493052142916112407554427 739578214374168611331641)
            ·
              refine ⟨554683660780626458498731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739578214374168611331641 554683660780626458498731)
              ·
                refine ⟨832025491170939687748097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554683660780626458498731 832025491170939687748097)
                ·
                  refine ⟨624019118378204765811073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 832025491170939687748097 624019118378204765811073)
                  ·
                    refine ⟨468014338783653574358305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624019118378204765811073 468014338783653574358305)
                    ·
                      refine ⟨351010754087740180768729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468014338783653574358305 351010754087740180768729)
                      ·
                        rfl

theorem cell23_683591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_683591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683591 prefixEnd_683591 := by exact prefixLift 683591
  have htrace : WordTrace (prefixWord ++ tailWord_683591) baseStart_683591 baseEnd_683591 := by
    simpa [prefixWord, tailWord_683591, baseEnd_683591] using wordTrace_append hprefix tailTrace_683591
  have hstable : (prefixWord ++ tailWord_683591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683591).length < 2 ^ (prefixWord ++ tailWord_683591).sum := by decide
  have hdescent : baseEnd_683591 < baseStart_683591 := by decide
  rcases family_descends (prefixWord ++ tailWord_683591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683683 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 1, 5]
def baseStart_683683 : Nat := 118140960795 + 683683 * 2 ^ 59
def prefixEnd_683683 : Nat := 4983230072969 + 3 ^ 40 * 683683 * 2
def baseEnd_683683 : Nat := 117019331435984606939435

theorem tailTrace_683683 : CollatzResearch.WordTrace tailWord_683683 prefixEnd_683683 117019331435984606939435 := by
  unfold tailWord_683683
  simp only [CollatzResearch.WordTrace]
  refine ⟨24935967582140729605471703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16623978388093819736981135 24935967582140729605471703)
  ·
    refine ⟨37403951373211094408207555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24935967582140729605471703 37403951373211094408207555)
    ·
      refine ⟨56105927059816641612311333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37403951373211094408207555 56105927059816641612311333)
      ·
        refine ⟨10519861323715620302308375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56105927059816641612311333 10519861323715620302308375)
        ·
          refine ⟨15779791985573430453462563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10519861323715620302308375 15779791985573430453462563)
          ·
            refine ⟨23669687978360145680193845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15779791985573430453462563 23669687978360145680193845)
            ·
              refine ⟨2219033247971263657518173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23669687978360145680193845 2219033247971263657518173)
              ·
                refine ⟨832137467989223871569315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2219033247971263657518173 832137467989223871569315)
                ·
                  refine ⟨1248206201983835807353973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832137467989223871569315 1248206201983835807353973)
                  ·
                    refine ⟨117019331435984606939435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1248206201983835807353973 117019331435984606939435)
                    ·
                      rfl

theorem cell23_683683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 5].length) (baseStart_683683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683683 prefixEnd_683683 := by exact prefixLift 683683
  have htrace : WordTrace (prefixWord ++ tailWord_683683) baseStart_683683 baseEnd_683683 := by
    simpa [prefixWord, tailWord_683683, baseEnd_683683] using wordTrace_append hprefix tailTrace_683683
  have hstable : (prefixWord ++ tailWord_683683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683683).length < 2 ^ (prefixWord ++ tailWord_683683).sum := by decide
  have hdescent : baseEnd_683683 < baseStart_683683 := by decide
  rcases family_descends (prefixWord ++ tailWord_683683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683696 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_683696 : Nat := 118140960795 + 683696 * 2 ^ 59
def prefixEnd_683696 : Nat := 4983230072969 + 3 ^ 40 * 683696 * 2
def baseEnd_683696 : Nat := 117021556518820756651915

theorem tailTrace_683696 : CollatzResearch.WordTrace tailWord_683696 prefixEnd_683696 117021556518820756651915 := by
  unfold tailWord_683696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468220865546816412847471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16624294487395755217129961 12468220865546816412847471)
  ·
    refine ⟨18702331298320224619271207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12468220865546816412847471 18702331298320224619271207)
    ·
      refine ⟨28053496947480336928906811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18702331298320224619271207 28053496947480336928906811)
      ·
        refine ⟨42080245421220505393360217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28053496947480336928906811 42080245421220505393360217)
        ·
          refine ⟨31560184065915379045020163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42080245421220505393360217 31560184065915379045020163)
          ·
            refine ⟨47340276098873068567530245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31560184065915379045020163 47340276098873068567530245)
            ·
              refine ⟨8876301768538700356411921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47340276098873068567530245 8876301768538700356411921)
              ·
                refine ⟨6657226326404025267308941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8876301768538700356411921 6657226326404025267308941)
                ·
                  refine ⟨2496459872401509475240853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6657226326404025267308941 2496459872401509475240853)
                  ·
                    refine ⟨117021556518820756651915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2496459872401509475240853 117021556518820756651915)
                    ·
                      rfl

theorem cell23_683696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_683696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683696 prefixEnd_683696 := by exact prefixLift 683696
  have htrace : WordTrace (prefixWord ++ tailWord_683696) baseStart_683696 baseEnd_683696 := by
    simpa [prefixWord, tailWord_683696, baseEnd_683696] using wordTrace_append hprefix tailTrace_683696
  have hstable : (prefixWord ++ tailWord_683696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683696).length < 2 ^ (prefixWord ++ tailWord_683696).sum := by decide
  have hdescent : baseEnd_683696 < baseStart_683696 := by decide
  rcases family_descends (prefixWord ++ tailWord_683696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683720 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_683720 : Nat := 118140960795 + 683720 * 2 ^ 59
def prefixEnd_683720 : Nat := 4983230072969 + 3 ^ 40 * 683720 * 2
def baseEnd_683720 : Nat := 351076993092170176055635

theorem tailTrace_683720 : CollatzResearch.WordTrace tailWord_683720 prefixEnd_683720 351076993092170176055635 := by
  unfold tailWord_683720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468658541503342462284307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16624878055337789949712409 12468658541503342462284307)
  ·
    refine ⟨18702987812255013693426461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12468658541503342462284307 18702987812255013693426461)
    ·
      refine ⟨7013620429595630135034923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18702987812255013693426461 7013620429595630135034923)
      ·
        refine ⟨10520430644393445202552385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7013620429595630135034923 10520430644393445202552385)
        ·
          refine ⟨7890322983295083901914289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10520430644393445202552385 7890322983295083901914289)
          ·
            refine ⟨5917742237471312926435717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7890322983295083901914289 5917742237471312926435717)
            ·
              refine ⟨1109576669525871173706697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5917742237471312926435717 1109576669525871173706697)
              ·
                refine ⟨832182502144403380280023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109576669525871173706697 832182502144403380280023)
                ·
                  refine ⟨1248273753216605070420035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832182502144403380280023 1248273753216605070420035)
                  ·
                    refine ⟨1872410629824907605630053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248273753216605070420035 1872410629824907605630053)
                    ·
                      refine ⟨351076993092170176055635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1872410629824907605630053 351076993092170176055635)
                      ·
                        rfl

theorem cell23_683720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_683720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683720 prefixEnd_683720 := by exact prefixLift 683720
  have htrace : WordTrace (prefixWord ++ tailWord_683720) baseStart_683720 baseEnd_683720 := by
    simpa [prefixWord, tailWord_683720, baseEnd_683720] using wordTrace_append hprefix tailTrace_683720
  have hstable : (prefixWord ++ tailWord_683720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683720).length < 2 ^ (prefixWord ++ tailWord_683720).sum := by decide
  have hdescent : baseEnd_683720 < baseStart_683720 := by decide
  rcases family_descends (prefixWord ++ tailWord_683720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683723 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3]
def baseStart_683723 : Nat := 118140960795 + 683723 * 2 ^ 59
def prefixEnd_683723 : Nat := 4983230072969 + 3 ^ 40 * 683723 * 2
def baseEnd_683723 : Nat := 351078533534133664318121

theorem tailTrace_683723 : CollatzResearch.WordTrace tailWord_683723 prefixEnd_683723 351078533534133664318121 := by
  unfold tailWord_683723
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937426501995816436927823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16624951001330544291285215 24937426501995816436927823)
  ·
    refine ⟨37406139752993724655391735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24937426501995816436927823 37406139752993724655391735)
    ·
      refine ⟨56109209629490586983087603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37406139752993724655391735 56109209629490586983087603)
      ·
        refine ⟨84163814444235880474631405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56109209629490586983087603 84163814444235880474631405)
        ·
          refine ⟨31561430416588455177986777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84163814444235880474631405 31561430416588455177986777)
          ·
            refine ⟨23671072812441341383490083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31561430416588455177986777 23671072812441341383490083)
            ·
              refine ⟨35506609218662012075235125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23671072812441341383490083 35506609218662012075235125)
              ·
                refine ⟨3328744614249563632053293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35506609218662012075235125 3328744614249563632053293)
                ·
                  refine ⟨1248279230343586362019985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3328744614249563632053293 1248279230343586362019985)
                  ·
                    refine ⟨936209422757689771514989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248279230343586362019985 936209422757689771514989)
                    ·
                      refine ⟨351078533534133664318121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 936209422757689771514989 351078533534133664318121)
                      ·
                        rfl

theorem cell23_683723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3].length) (baseStart_683723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683723 prefixEnd_683723 := by exact prefixLift 683723
  have htrace : WordTrace (prefixWord ++ tailWord_683723) baseStart_683723 baseEnd_683723 := by
    simpa [prefixWord, tailWord_683723, baseEnd_683723] using wordTrace_append hprefix tailTrace_683723
  have hstable : (prefixWord ++ tailWord_683723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683723).length < 2 ^ (prefixWord ++ tailWord_683723).sum := by decide
  have hdescent : baseEnd_683723 < baseStart_683723 := by decide
  rcases family_descends (prefixWord ++ tailWord_683723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683730 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_683730 : Nat := 118140960795 + 683730 * 2 ^ 59
def prefixEnd_683730 : Nat := 4983230072969 + 3 ^ 40 * 683730 * 2
def baseEnd_683730 : Nat := 117027375966238378976863

theorem tailTrace_683730 : CollatzResearch.WordTrace tailWord_683730 prefixEnd_683730 117027375966238378976863 := by
  unfold tailWord_683730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234420453242614158108161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16625121208646971088288429 6234420453242614158108161)
  ·
    refine ⟨4675815339931960618581121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6234420453242614158108161 4675815339931960618581121)
    ·
      refine ⟨3506861504948970463935841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4675815339931960618581121 3506861504948970463935841)
      ·
        refine ⟨2630146128711727847951881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3506861504948970463935841 2630146128711727847951881)
        ·
          refine ⟨1972609596533795885963911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2630146128711727847951881 1972609596533795885963911)
          ·
            refine ⟨2958914394800693828945867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972609596533795885963911 2958914394800693828945867)
            ·
              refine ⟨4438371592201040743418801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958914394800693828945867 4438371592201040743418801)
              ·
                refine ⟨3328778694150780557564101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438371592201040743418801 3328778694150780557564101)
                ·
                  refine ⟨624146005153271354543269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3328778694150780557564101 624146005153271354543269)
                  ·
                    refine ⟨117027375966238378976863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624146005153271354543269 117027375966238378976863)
                    ·
                      rfl

theorem cell23_683730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_683730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683730 prefixEnd_683730 := by exact prefixLift 683730
  have htrace : WordTrace (prefixWord ++ tailWord_683730) baseStart_683730 baseEnd_683730 := by
    simpa [prefixWord, tailWord_683730, baseEnd_683730] using wordTrace_append hprefix tailTrace_683730
  have hstable : (prefixWord ++ tailWord_683730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683730).length < 2 ^ (prefixWord ++ tailWord_683730).sum := by decide
  have hdescent : baseEnd_683730 < baseStart_683730 := by decide
  rcases family_descends (prefixWord ++ tailWord_683730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683754 : List Nat := [3, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_683754 : Nat := 118140960795 + 683754 * 2 ^ 59
def prefixEnd_683754 : Nat := 4983230072969 + 3 ^ 40 * 683754 * 2
def baseEnd_683754 : Nat := 351094451434423043030479

theorem tailTrace_683754 : CollatzResearch.WordTrace tailWord_683754 prefixEnd_683754 351094451434423043030479 := by
  unfold tailWord_683754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234639291220877182826579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16625704776589005820870877 6234639291220877182826579)
  ·
    refine ⟨9351958936831315774239869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6234639291220877182826579 9351958936831315774239869)
    ·
      refine ⟨3506984601311743415339951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9351958936831315774239869 3506984601311743415339951)
      ·
        refine ⟨5260476901967615123009927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506984601311743415339951 5260476901967615123009927)
        ·
          refine ⟨7890715352951422684514891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260476901967615123009927 7890715352951422684514891)
          ·
            refine ⟨11836073029427134026772337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890715352951422684514891 11836073029427134026772337)
            ·
              refine ⟨8877054772070350520079253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11836073029427134026772337 8877054772070350520079253)
              ·
                refine ⟨416111942440797680628715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8877054772070350520079253 416111942440797680628715)
                ·
                  refine ⟨624167913661196520943073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416111942440797680628715 624167913661196520943073)
                  ·
                    refine ⟨468125935245897390707305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624167913661196520943073 468125935245897390707305)
                    ·
                      refine ⟨351094451434423043030479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468125935245897390707305 351094451434423043030479)
                      ·
                        rfl

theorem cell23_683754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_683754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683754 prefixEnd_683754 := by exact prefixLift 683754
  have htrace : WordTrace (prefixWord ++ tailWord_683754) baseStart_683754 baseEnd_683754 := by
    simpa [prefixWord, tailWord_683754, baseEnd_683754] using wordTrace_append hprefix tailTrace_683754
  have hstable : (prefixWord ++ tailWord_683754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683754).length < 2 ^ (prefixWord ++ tailWord_683754).sum := by decide
  have hdescent : baseEnd_683754 < baseStart_683754 := by decide
  rcases family_descends (prefixWord ++ tailWord_683754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683823 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_683823 : Nat := 118140960795 + 683823 * 2 ^ 59
def prefixEnd_683823 : Nat := 4983230072969 + 3 ^ 40 * 683823 * 2
def baseEnd_683823 : Nat := 351129881599583273067661

theorem tailTrace_683823 : CollatzResearch.WordTrace tailWord_683823 prefixEnd_683823 351129881599583273067661 := by
  unfold tailWord_683823
  simp only [CollatzResearch.WordTrace]
  refine ⟨24941073801633533515568123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16627382534422355677045415 24941073801633533515568123)
  ·
    refine ⟨37411610702450300273352185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24941073801633533515568123 37411610702450300273352185)
    ·
      refine ⟨28058708026837725205014139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37411610702450300273352185 28058708026837725205014139)
      ·
        refine ⟨42088062040256587807521209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28058708026837725205014139 42088062040256587807521209)
        ·
          refine ⟨31566046530192440855640907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42088062040256587807521209 31566046530192440855640907)
          ·
            refine ⟨47349069795288661283461361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31566046530192440855640907 47349069795288661283461361)
            ·
              refine ⟨35511802346466495962596021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47349069795288661283461361 35511802346466495962596021)
              ·
                refine ⟨3329231469981233996493377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35511802346466495962596021 3329231469981233996493377)
                ·
                  refine ⟨2496923602485925497370033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329231469981233996493377 2496923602485925497370033)
                  ·
                    refine ⟨1872692701864444123027525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496923602485925497370033 1872692701864444123027525)
                    ·
                      refine ⟨351129881599583273067661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1872692701864444123027525 351129881599583273067661)
                      ·
                        rfl

theorem cell23_683823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_683823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683823 prefixEnd_683823 := by exact prefixLift 683823
  have htrace : WordTrace (prefixWord ++ tailWord_683823) baseStart_683823 baseEnd_683823 := by
    simpa [prefixWord, tailWord_683823, baseEnd_683823] using wordTrace_append hprefix tailTrace_683823
  have hstable : (prefixWord ++ tailWord_683823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683823).length < 2 ^ (prefixWord ++ tailWord_683823).sum := by decide
  have hdescent : baseEnd_683823 < baseStart_683823 := by decide
  rcases family_descends (prefixWord ++ tailWord_683823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683861 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_683861 : Nat := 118140960795 + 683861 * 2 ^ 59
def prefixEnd_683861 : Nat := 4983230072969 + 3 ^ 40 * 683861 * 2
def baseEnd_683861 : Nat := 351149393864454124392487

theorem tailTrace_683861 : CollatzResearch.WordTrace tailWord_683861 prefixEnd_683861 351149393864454124392487 := by
  unfold tailWord_683861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942459775495866005451437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16628306516997244003634291 24942459775495866005451437)
  ·
    refine ⟨9353422415810949752044289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24942459775495866005451437 9353422415810949752044289)
    ·
      refine ⟨7015066811858212314033217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9353422415810949752044289 7015066811858212314033217)
      ·
        refine ⟨5261300108893659235524913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7015066811858212314033217 5261300108893659235524913)
        ·
          refine ⟨3945975081670244426643685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5261300108893659235524913 3945975081670244426643685)
          ·
            refine ⟨739870327813170829995691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3945975081670244426643685 739870327813170829995691)
            ·
              refine ⟨1109805491719756244993537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739870327813170829995691 1109805491719756244993537)
              ·
                refine ⟨832354118789817183745153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109805491719756244993537 832354118789817183745153)
                ·
                  refine ⟨624265589092362887808865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 832354118789817183745153 624265589092362887808865)
                  ·
                    refine ⟨468199191819272165856649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624265589092362887808865 468199191819272165856649)
                    ·
                      refine ⟨351149393864454124392487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468199191819272165856649 351149393864454124392487)
                      ·
                        rfl

theorem cell23_683861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_683861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683861 prefixEnd_683861 := by exact prefixLift 683861
  have htrace : WordTrace (prefixWord ++ tailWord_683861) baseStart_683861 baseEnd_683861 := by
    simpa [prefixWord, tailWord_683861, baseEnd_683861] using wordTrace_append hprefix tailTrace_683861
  have hstable : (prefixWord ++ tailWord_683861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683861).length < 2 ^ (prefixWord ++ tailWord_683861).sum := by decide
  have hdescent : baseEnd_683861 < baseStart_683861 := by decide
  rcases family_descends (prefixWord ++ tailWord_683861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683873 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_683873 : Nat := 118140960795 + 683873 * 2 ^ 59
def prefixEnd_683873 : Nat := 4983230072969 + 3 ^ 40 * 683873 * 2
def baseEnd_683873 : Nat := 351155555632308077442431

theorem tailTrace_683873 : CollatzResearch.WordTrace tailWord_683873 prefixEnd_683873 351155555632308077442431 := by
  unfold tailWord_683873
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942897451452392054888273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16628598300968261369925515 24942897451452392054888273)
  ·
    refine ⟨18707173088589294041166205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24942897451452392054888273 18707173088589294041166205)
    ·
      refine ⟨7015189908220985265437327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18707173088589294041166205 7015189908220985265437327)
      ·
        refine ⟨10522784862331477898155991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7015189908220985265437327 10522784862331477898155991)
        ·
          refine ⟨15784177293497216847233987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10522784862331477898155991 15784177293497216847233987)
          ·
            refine ⟨23676265940245825270850981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15784177293497216847233987 23676265940245825270850981)
            ·
              refine ⟨4439299863796092238284559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23676265940245825270850981 4439299863796092238284559)
              ·
                refine ⟨6658949795694138357426839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439299863796092238284559 6658949795694138357426839)
                ·
                  refine ⟨9988424693541207536140259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6658949795694138357426839 9988424693541207536140259)
                  ·
                    refine ⟨14982637040311811304210389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9988424693541207536140259 14982637040311811304210389)
                    ·
                      refine ⟨351155555632308077442431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14982637040311811304210389 351155555632308077442431)
                      ·
                        rfl

theorem cell23_683873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_683873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683873 prefixEnd_683873 := by exact prefixLift 683873
  have htrace : WordTrace (prefixWord ++ tailWord_683873) baseStart_683873 baseEnd_683873 := by
    simpa [prefixWord, tailWord_683873, baseEnd_683873] using wordTrace_append hprefix tailTrace_683873
  have hstable : (prefixWord ++ tailWord_683873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683873).length < 2 ^ (prefixWord ++ tailWord_683873).sum := by decide
  have hdescent : baseEnd_683873 < baseStart_683873 := by decide
  rcases family_descends (prefixWord ++ tailWord_683873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683903 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_683903 : Nat := 118140960795 + 683903 * 2 ^ 59
def prefixEnd_683903 : Nat := 4983230072969 + 3 ^ 40 * 683903 * 2
def baseEnd_683903 : Nat := 351170960051942960067293

theorem tailTrace_683903 : CollatzResearch.WordTrace tailWord_683903 prefixEnd_683903 351170960051942960067293 := by
  unfold tailWord_683903
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943991641343707178480363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16629327760895804785653575 24943991641343707178480363)
  ·
    refine ⟨37415987462015560767720545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24943991641343707178480363 37415987462015560767720545)
    ·
      refine ⟨28061990596511670575790409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37415987462015560767720545 28061990596511670575790409)
      ·
        refine ⟨21046492947383752931842807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28061990596511670575790409 21046492947383752931842807)
        ·
          refine ⟨31569739421075629397764211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21046492947383752931842807 31569739421075629397764211)
          ·
            refine ⟨47354609131613444096646317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31569739421075629397764211 47354609131613444096646317)
            ·
              refine ⟨17757978424355041536242369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47354609131613444096646317 17757978424355041536242369)
              ·
                refine ⟨13318483818266281152181777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17757978424355041536242369 13318483818266281152181777)
                ·
                  refine ⟨9988862863699710864136333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13318483818266281152181777 9988862863699710864136333)
                  ·
                    refine ⟨3745823573887391574051125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9988862863699710864136333 3745823573887391574051125)
                    ·
                      refine ⟨351170960051942960067293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3745823573887391574051125 351170960051942960067293)
                      ·
                        rfl

theorem cell23_683903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_683903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683903 prefixEnd_683903 := by exact prefixLift 683903
  have htrace : WordTrace (prefixWord ++ tailWord_683903) baseStart_683903 baseEnd_683903 := by
    simpa [prefixWord, tailWord_683903, baseEnd_683903] using wordTrace_append hprefix tailTrace_683903
  have hstable : (prefixWord ++ tailWord_683903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683903).length < 2 ^ (prefixWord ++ tailWord_683903).sum := by decide
  have hdescent : baseEnd_683903 < baseStart_683903 := by decide
  rcases family_descends (prefixWord ++ tailWord_683903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683920 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_683920 : Nat := 118140960795 + 683920 * 2 ^ 59
def prefixEnd_683920 : Nat := 4983230072969 + 3 ^ 40 * 683920 * 2
def baseEnd_683920 : Nat := 351179689223069393554715

theorem tailTrace_683920 : CollatzResearch.WordTrace tailWord_683920 prefixEnd_683920 351179689223069393554715 := by
  unfold tailWord_683920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472305841141059540924607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16629741121521412721232809 12472305841141059540924607)
  ·
    refine ⟨18708458761711589311386911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12472305841141059540924607 18708458761711589311386911)
    ·
      refine ⟨28062688142567383967080367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18708458761711589311386911 28062688142567383967080367)
      ·
        refine ⟨42094032213851075950620551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28062688142567383967080367 42094032213851075950620551)
        ·
          refine ⟨63141048320776613925930827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42094032213851075950620551 63141048320776613925930827)
          ·
            refine ⟨94711572481164920888896241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63141048320776613925930827 94711572481164920888896241)
            ·
              refine ⟨71033679360873690666672181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94711572481164920888896241 71033679360873690666672181)
              ·
                refine ⟨6659407440081908500000517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71033679360873690666672181 6659407440081908500000517)
                ·
                  refine ⟨1248638895015357843750097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6659407440081908500000517 1248638895015357843750097)
                  ·
                    refine ⟨936479171261518382812573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248638895015357843750097 936479171261518382812573)
                    ·
                      refine ⟨351179689223069393554715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 936479171261518382812573 351179689223069393554715)
                      ·
                        rfl

theorem cell23_683920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_683920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683920 prefixEnd_683920 := by exact prefixLift 683920
  have htrace : WordTrace (prefixWord ++ tailWord_683920) baseStart_683920 baseEnd_683920 := by
    simpa [prefixWord, tailWord_683920, baseEnd_683920] using wordTrace_append hprefix tailTrace_683920
  have hstable : (prefixWord ++ tailWord_683920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683920).length < 2 ^ (prefixWord ++ tailWord_683920).sum := by decide
  have hdescent : baseEnd_683920 < baseStart_683920 := by decide
  rcases family_descends (prefixWord ++ tailWord_683920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683927 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 3, 4]
def baseStart_683927 : Nat := 118140960795 + 683927 * 2 ^ 59
def prefixEnd_683927 : Nat := 4983230072969 + 3 ^ 40 * 683927 * 2
def baseEnd_683927 : Nat := 117061094529216955389061

theorem tailTrace_683927 : CollatzResearch.WordTrace tailWord_683927 prefixEnd_683927 117061094529216955389061 := by
  unfold tailWord_683927
  simp only [CollatzResearch.WordTrace]
  refine ⟨24944866993256759277354035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16629911328837839518236023 24944866993256759277354035)
  ·
    refine ⟨37417300489885138916031053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24944866993256759277354035 37417300489885138916031053)
    ·
      refine ⟨14031487683706927093511645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37417300489885138916031053 14031487683706927093511645)
      ·
        refine ⟨5261807881390097660066867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14031487683706927093511645 5261807881390097660066867)
        ·
          refine ⟨7892711822085146490100301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261807881390097660066867 7892711822085146490100301)
          ·
            refine ⟨2959766933281929933787613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7892711822085146490100301 2959766933281929933787613)
            ·
              refine ⟨1109912599980723725170355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959766933281929933787613 1109912599980723725170355)
              ·
                refine ⟨1664868899971085587755533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109912599980723725170355 1664868899971085587755533)
                ·
                  refine ⟨624325837489157095408325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1664868899971085587755533 624325837489157095408325)
                  ·
                    refine ⟨117061094529216955389061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624325837489157095408325 117061094529216955389061)
                    ·
                      rfl

theorem cell23_683927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_683927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_683927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_683927 prefixEnd_683927 := by exact prefixLift 683927
  have htrace : WordTrace (prefixWord ++ tailWord_683927) baseStart_683927 baseEnd_683927 := by
    simpa [prefixWord, tailWord_683927, baseEnd_683927] using wordTrace_append hprefix tailTrace_683927
  have hstable : (prefixWord ++ tailWord_683927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683927).length < 2 ^ (prefixWord ++ tailWord_683927).sum := by decide
  have hdescent : baseEnd_683927 < baseStart_683927 := by decide
  rcases family_descends (prefixWord ++ tailWord_683927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684024 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_684024 : Nat := 118140960795 + 684024 * 2 ^ 59
def prefixEnd_684024 : Nat := 4983230072969 + 3 ^ 40 * 684024 * 2
def baseEnd_684024 : Nat := 351233091211136986654237

theorem tailTrace_684024 : CollatzResearch.WordTrace tailWord_684024 prefixEnd_684024 351233091211136986654237 := by
  unfold tailWord_684024
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474202436952672421817563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16632269915936896562423417 12474202436952672421817563)
  ·
    refine ⟨18711303655429008632726345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12474202436952672421817563 18711303655429008632726345)
    ·
      refine ⟨14033477741571756474544759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18711303655429008632726345 14033477741571756474544759)
      ·
        refine ⟨21050216612357634711817139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14033477741571756474544759 21050216612357634711817139)
        ·
          refine ⟨31575324918536452067725709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21050216612357634711817139 31575324918536452067725709)
          ·
            refine ⟨11840746844451169525397141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31575324918536452067725709 11840746844451169525397141)
            ·
              refine ⟨555035008333648571502991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11840746844451169525397141 555035008333648571502991)
              ·
                refine ⟨832552512500472857254487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555035008333648571502991 832552512500472857254487)
                ·
                  refine ⟨1248828768750709285881731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832552512500472857254487 1248828768750709285881731)
                  ·
                    refine ⟨1873243153126063928822597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248828768750709285881731 1873243153126063928822597)
                    ·
                      refine ⟨351233091211136986654237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1873243153126063928822597 351233091211136986654237)
                      ·
                        rfl

theorem cell23_684024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_684024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684024 prefixEnd_684024 := by exact prefixLift 684024
  have htrace : WordTrace (prefixWord ++ tailWord_684024) baseStart_684024 baseEnd_684024 := by
    simpa [prefixWord, tailWord_684024, baseEnd_684024] using wordTrace_append hprefix tailTrace_684024
  have hstable : (prefixWord ++ tailWord_684024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684024).length < 2 ^ (prefixWord ++ tailWord_684024).sum := by decide
  have hdescent : baseEnd_684024 < baseStart_684024 := by decide
  rcases family_descends (prefixWord ++ tailWord_684024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684061 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_684061 : Nat := 118140960795 + 684061 * 2 ^ 59
def prefixEnd_684061 : Nat := 4983230072969 + 3 ^ 40 * 684061 * 2
def baseEnd_684061 : Nat := 351252089995353341891567

theorem tailTrace_684061 : CollatzResearch.WordTrace tailWord_684061 prefixEnd_684061 351252089995353341891567 := by
  unfold tailWord_684061
  simp only [CollatzResearch.WordTrace]
  refine ⟨24949754374771300162732037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16633169583180866775154691 24949754374771300162732037)
  ·
    refine ⟨4678078945269618780512257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24949754374771300162732037 4678078945269618780512257)
    ·
      refine ⟨3508559208952214085384193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4678078945269618780512257 3508559208952214085384193)
      ·
        refine ⟨2631419406714160564038145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3508559208952214085384193 2631419406714160564038145)
        ·
          refine ⟨1973564555035620423028609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631419406714160564038145 1973564555035620423028609)
          ·
            refine ⟨1480173416276715317271457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973564555035620423028609 1480173416276715317271457)
            ·
              refine ⟨1110130062207536487953593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480173416276715317271457 1110130062207536487953593)
              ·
                refine ⟨832597546655652365965195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110130062207536487953593 832597546655652365965195)
                ·
                  refine ⟨1248896319983478548947793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832597546655652365965195 1248896319983478548947793)
                  ·
                    refine ⟨936672239987608911710845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248896319983478548947793 936672239987608911710845)
                    ·
                      refine ⟨351252089995353341891567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 936672239987608911710845 351252089995353341891567)
                      ·
                        rfl

theorem cell23_684061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_684061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684061 prefixEnd_684061 := by exact prefixLift 684061
  have htrace : WordTrace (prefixWord ++ tailWord_684061) baseStart_684061 baseEnd_684061 := by
    simpa [prefixWord, tailWord_684061, baseEnd_684061] using wordTrace_append hprefix tailTrace_684061
  have hstable : (prefixWord ++ tailWord_684061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684061).length < 2 ^ (prefixWord ++ tailWord_684061).sum := by decide
  have hdescent : baseEnd_684061 < baseStart_684061 := by decide
  rcases family_descends (prefixWord ++ tailWord_684061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684117 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_684117 : Nat := 118140960795 + 684117 * 2 ^ 59
def prefixEnd_684117 : Nat := 4983230072969 + 3 ^ 40 * 684117 * 2
def baseEnd_684117 : Nat := 351280844912005122791309

theorem tailTrace_684117 : CollatzResearch.WordTrace tailWord_684117 prefixEnd_684117 351280844912005122791309 := by
  unfold tailWord_684117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24951796862568421726770605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16634531241712281151180403 24951796862568421726770605)
  ·
    refine ⟨9356923823463158147538977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24951796862568421726770605 9356923823463158147538977)
    ·
      refine ⟨7017692867597368610654233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9356923823463158147538977 7017692867597368610654233)
      ·
        refine ⟨5263269650698026457990675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7017692867597368610654233 5263269650698026457990675)
        ·
          refine ⟨7894904476047039686986013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263269650698026457990675 7894904476047039686986013)
          ·
            refine ⟨2960589178517639882619755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7894904476047039686986013 2960589178517639882619755)
            ·
              refine ⟨4440883767776459823929633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960589178517639882619755 4440883767776459823929633)
              ·
                refine ⟨3330662825832344867947225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4440883767776459823929633 3330662825832344867947225)
                ·
                  refine ⟨2497997119374258650960419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330662825832344867947225 2497997119374258650960419)
                  ·
                    refine ⟨3746995679061387976440629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497997119374258650960419 3746995679061387976440629)
                    ·
                      refine ⟨351280844912005122791309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3746995679061387976440629 351280844912005122791309)
                      ·
                        rfl

theorem cell23_684117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_684117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684117 prefixEnd_684117 := by exact prefixLift 684117
  have htrace : WordTrace (prefixWord ++ tailWord_684117) baseStart_684117 baseEnd_684117 := by
    simpa [prefixWord, tailWord_684117, baseEnd_684117] using wordTrace_append hprefix tailTrace_684117
  have hstable : (prefixWord ++ tailWord_684117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684117).length < 2 ^ (prefixWord ++ tailWord_684117).sum := by decide
  have hdescent : baseEnd_684117 < baseStart_684117 := by decide
  rcases family_descends (prefixWord ++ tailWord_684117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684164 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_684164 : Nat := 118140960795 + 684164 * 2 ^ 59
def prefixEnd_684164 : Nat := 4983230072969 + 3 ^ 40 * 684164 * 2
def baseEnd_684164 : Nat := 351304978502766438903593

theorem tailTrace_684164 : CollatzResearch.WordTrace tailWord_684164 prefixEnd_684164 351304978502766438903593 := by
  unfold tailWord_684164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476755546699074376865773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16635674062265432502487697 12476755546699074376865773)
  ·
    refine ⟨4678783330012152891324665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12476755546699074376865773 4678783330012152891324665)
    ·
      refine ⟨3509087497509114668493499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4678783330012152891324665 3509087497509114668493499)
      ·
        refine ⟨5263631246263672002740249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509087497509114668493499 5263631246263672002740249)
        ·
          refine ⟨3947723434697754002055187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5263631246263672002740249 3947723434697754002055187)
          ·
            refine ⟨5921585152046631003082781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947723434697754002055187 5921585152046631003082781)
            ·
              refine ⟨2220594432017486626156043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5921585152046631003082781 2220594432017486626156043)
              ·
                refine ⟨3330891648026229939234065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220594432017486626156043 3330891648026229939234065)
                ·
                  refine ⟨2498168736019672454425549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330891648026229939234065 2498168736019672454425549)
                  ·
                    refine ⟨936813276007377170409581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498168736019672454425549 936813276007377170409581)
                    ·
                      refine ⟨351304978502766438903593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 936813276007377170409581 351304978502766438903593)
                      ·
                        rfl

theorem cell23_684164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_684164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684164 prefixEnd_684164 := by exact prefixLift 684164
  have htrace : WordTrace (prefixWord ++ tailWord_684164) baseStart_684164 baseEnd_684164 := by
    simpa [prefixWord, tailWord_684164, baseEnd_684164] using wordTrace_append hprefix tailTrace_684164
  have hstable : (prefixWord ++ tailWord_684164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684164).length < 2 ^ (prefixWord ++ tailWord_684164).sum := by decide
  have hdescent : baseEnd_684164 < baseStart_684164 := by decide
  rcases family_descends (prefixWord ++ tailWord_684164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684167 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 4, 5]
def baseStart_684167 : Nat := 118140960795 + 684167 * 2 ^ 59
def prefixEnd_684167 : Nat := 4983230072969 + 3 ^ 40 * 684167 * 2
def baseEnd_684167 : Nat := 117102172981576642388693

theorem tailTrace_684167 : CollatzResearch.WordTrace tailWord_684167 prefixEnd_684167 117102172981576642388693 := by
  unfold tailWord_684167
  simp only [CollatzResearch.WordTrace]
  refine ⟨24953620512387280266090755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16635747008258186844060503 24953620512387280266090755)
  ·
    refine ⟨37430430768580920399136133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24953620512387280266090755 37430430768580920399136133)
    ·
      refine ⟨7018205769108922574838025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37430430768580920399136133 7018205769108922574838025)
      ·
        refine ⟨5263654326831691931128519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7018205769108922574838025 5263654326831691931128519)
        ·
          refine ⟨7895481490247537896692779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263654326831691931128519 7895481490247537896692779)
          ·
            refine ⟨11843222235371306845039169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7895481490247537896692779 11843222235371306845039169)
            ·
              refine ⟨8882416676528480133779377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11843222235371306845039169 8882416676528480133779377)
              ·
                refine ⟨6661812507396360100334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8882416676528480133779377 6661812507396360100334533)
                ·
                  refine ⟨1249089845136817518812725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6661812507396360100334533 1249089845136817518812725)
                  ·
                    refine ⟨117102172981576642388693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1249089845136817518812725 117102172981576642388693)
                    ·
                      rfl

theorem cell23_684167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_684167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684167 prefixEnd_684167 := by exact prefixLift 684167
  have htrace : WordTrace (prefixWord ++ tailWord_684167) baseStart_684167 baseEnd_684167 := by
    simpa [prefixWord, tailWord_684167, baseEnd_684167] using wordTrace_append hprefix tailTrace_684167
  have hstable : (prefixWord ++ tailWord_684167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684167).length < 2 ^ (prefixWord ++ tailWord_684167).sum := by decide
  have hdescent : baseEnd_684167 < baseStart_684167 := by decide
  rcases family_descends (prefixWord ++ tailWord_684167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684184 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_684184 : Nat := 118140960795 + 684184 * 2 ^ 59
def prefixEnd_684184 : Nat := 4983230072969 + 3 ^ 40 * 684184 * 2
def baseEnd_684184 : Nat := 117105082705285453551167

theorem tailTrace_684184 : CollatzResearch.WordTrace tailWord_684184 prefixEnd_684184 117105082705285453551167 := by
  unfold tailWord_684184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477120276662846084729803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16636160368883794779639737 12477120276662846084729803)
  ·
    refine ⟨18715680414994269127094705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477120276662846084729803 18715680414994269127094705)
    ·
      refine ⟨14036760311245701845321029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18715680414994269127094705 14036760311245701845321029)
      ·
        refine ⟨2631892558358569095997693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14036760311245701845321029 2631892558358569095997693)
        ·
          refine ⟨986959709384463410999135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2631892558358569095997693 986959709384463410999135)
          ·
            refine ⟨1480439564076695116498703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986959709384463410999135 1480439564076695116498703)
            ·
              refine ⟨2220659346115042674748055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480439564076695116498703 2220659346115042674748055)
              ·
                refine ⟨3330989019172564012122083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220659346115042674748055 3330989019172564012122083)
                ·
                  refine ⟨4996483528758846018183125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330989019172564012122083 4996483528758846018183125)
                  ·
                    refine ⟨117105082705285453551167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4996483528758846018183125 117105082705285453551167)
                    ·
                      rfl

theorem cell23_684184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_684184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684184 prefixEnd_684184 := by exact prefixLift 684184
  have htrace : WordTrace (prefixWord ++ tailWord_684184) baseStart_684184 baseEnd_684184 := by
    simpa [prefixWord, tailWord_684184, baseEnd_684184] using wordTrace_append hprefix tailTrace_684184
  have hstable : (prefixWord ++ tailWord_684184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684184).length < 2 ^ (prefixWord ++ tailWord_684184).sum := by decide
  have hdescent : baseEnd_684184 < baseStart_684184 := by decide
  rcases family_descends (prefixWord ++ tailWord_684184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684187 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4]
def baseStart_684187 : Nat := 118140960795 + 684187 * 2 ^ 59
def prefixEnd_684187 : Nat := 4983230072969 + 3 ^ 40 * 684187 * 2
def baseEnd_684187 : Nat := 351316788557819848915987

theorem tailTrace_684187 : CollatzResearch.WordTrace tailWord_684187 prefixEnd_684187 351316788557819848915987 := by
  unfold tailWord_684187
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954349972314823681818815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16636233314876549121212543 24954349972314823681818815)
  ·
    refine ⟨37431524958472235522728223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24954349972314823681818815 37431524958472235522728223)
    ·
      refine ⟨56147287437708353284092335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37431524958472235522728223 56147287437708353284092335)
      ·
        refine ⟨84220931156562529926138503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56147287437708353284092335 84220931156562529926138503)
        ·
          refine ⟨126331396734843794889207755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84220931156562529926138503 126331396734843794889207755)
          ·
            refine ⟨189497095102265692333811633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126331396734843794889207755 189497095102265692333811633)
            ·
              refine ⟨142122821326699269250358725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189497095102265692333811633 142122821326699269250358725)
              ·
                refine ⟨26648028998756112984442261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142122821326699269250358725 26648028998756112984442261)
                ·
                  refine ⟨1249126359316692796145731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26648028998756112984442261 1249126359316692796145731)
                  ·
                    refine ⟨1873689538975039194218597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1249126359316692796145731 1873689538975039194218597)
                    ·
                      refine ⟨351316788557819848915987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1873689538975039194218597 351316788557819848915987)
                      ·
                        rfl

theorem cell23_684187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4].length) (baseStart_684187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684187 prefixEnd_684187 := by exact prefixLift 684187
  have htrace : WordTrace (prefixWord ++ tailWord_684187) baseStart_684187 baseEnd_684187 := by
    simpa [prefixWord, tailWord_684187, baseEnd_684187] using wordTrace_append hprefix tailTrace_684187
  have hstable : (prefixWord ++ tailWord_684187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684187).length < 2 ^ (prefixWord ++ tailWord_684187).sum := by decide
  have hdescent : baseEnd_684187 < baseStart_684187 := by decide
  rcases family_descends (prefixWord ++ tailWord_684187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684217 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 6]
def baseStart_684217 : Nat := 118140960795 + 684217 * 2 ^ 59
def prefixEnd_684217 : Nat := 4983230072969 + 3 ^ 40 * 684217 * 2
def baseEnd_684217 : Nat := 351332192977454731540849

theorem tailTrace_684217 : CollatzResearch.WordTrace tailWord_684217 prefixEnd_684217 351332192977454731540849 := by
  unfold tailWord_684217
  simp only [CollatzResearch.WordTrace]
  refine ⟨24955444162206138805410905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16636962774804092536940603 24955444162206138805410905)
  ·
    refine ⟨18716583121654604104058179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24955444162206138805410905 18716583121654604104058179)
    ·
      refine ⟨28074874682481906156087269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716583121654604104058179 28074874682481906156087269)
      ·
        refine ⟨5264039002965357404266363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28074874682481906156087269 5264039002965357404266363)
        ·
          refine ⟨7896058504448036106399545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264039002965357404266363 7896058504448036106399545)
          ·
            refine ⟨5922043878336027079799659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7896058504448036106399545 5922043878336027079799659)
            ·
              refine ⟨8883065817504040619699489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5922043878336027079799659 8883065817504040619699489)
              ·
                refine ⟨6662299363128030464774617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8883065817504040619699489 6662299363128030464774617)
                ·
                  refine ⟨4996724522346022848580963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6662299363128030464774617 4996724522346022848580963)
                  ·
                    refine ⟨7495086783519034272871445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4996724522346022848580963 7495086783519034272871445)
                    ·
                      refine ⟨351332192977454731540849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7495086783519034272871445 351332192977454731540849)
                      ·
                        rfl

theorem cell23_684217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_684217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684217 prefixEnd_684217 := by exact prefixLift 684217
  have htrace : WordTrace (prefixWord ++ tailWord_684217) baseStart_684217 baseEnd_684217 := by
    simpa [prefixWord, tailWord_684217, baseEnd_684217] using wordTrace_append hprefix tailTrace_684217
  have hstable : (prefixWord ++ tailWord_684217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684217).length < 2 ^ (prefixWord ++ tailWord_684217).sum := by decide
  have hdescent : baseEnd_684217 < baseStart_684217 := by decide
  rcases family_descends (prefixWord ++ tailWord_684217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684224 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_684224 : Nat := 118140960795 + 684224 * 2 ^ 59
def prefixEnd_684224 : Nat := 4983230072969 + 3 ^ 40 * 684224 * 2
def baseEnd_684224 : Nat := 351335787342036204153317

theorem tailTrace_684224 : CollatzResearch.WordTrace tailWord_684224 prefixEnd_684224 351335787342036204153317 := by
  unfold tailWord_684224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477849736590389500457863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16637132982120519333943817 12477849736590389500457863)
  ·
    refine ⟨18716774604885584250686795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477849736590389500457863 18716774604885584250686795)
    ·
      refine ⟨28075161907328376376030193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716774604885584250686795 28075161907328376376030193)
      ·
        refine ⟨21056371430496282282022645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28075161907328376376030193 21056371430496282282022645)
        ·
          refine ⟨1974034821609026463939623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21056371430496282282022645 1974034821609026463939623)
          ·
            refine ⟨2961052232413539695909435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974034821609026463939623 2961052232413539695909435)
            ·
              refine ⟨4441578348620309543864153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961052232413539695909435 4441578348620309543864153)
              ·
                refine ⟨3331183761465232157898115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441578348620309543864153 3331183761465232157898115)
                ·
                  refine ⟨4996775642197848236847173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331183761465232157898115 4996775642197848236847173)
                  ·
                    refine ⟨936895432912096544408845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996775642197848236847173 936895432912096544408845)
                    ·
                      refine ⟨351335787342036204153317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 936895432912096544408845 351335787342036204153317)
                      ·
                        rfl

theorem cell23_684224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_684224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684224 prefixEnd_684224 := by exact prefixLift 684224
  have htrace : WordTrace (prefixWord ++ tailWord_684224) baseStart_684224 baseEnd_684224 := by
    simpa [prefixWord, tailWord_684224, baseEnd_684224] using wordTrace_append hprefix tailTrace_684224
  have hstable : (prefixWord ++ tailWord_684224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684224).length < 2 ^ (prefixWord ++ tailWord_684224).sum := by decide
  have hdescent : baseEnd_684224 < baseStart_684224 := by decide
  rcases family_descends (prefixWord ++ tailWord_684224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684248 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 1, 4]
def baseStart_684248 : Nat := 118140960795 + 684248 * 2 ^ 59
def prefixEnd_684248 : Nat := 4983230072969 + 3 ^ 40 * 684248 * 2
def baseEnd_684248 : Nat := 117116036959248036751069

theorem tailTrace_684248 : CollatzResearch.WordTrace tailWord_684248 prefixEnd_684248 117116036959248036751069 := by
  unfold tailWord_684248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478287412546915549894699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16637716550062554066526265 12478287412546915549894699)
  ·
    refine ⟨18717431118820373324842049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12478287412546915549894699 18717431118820373324842049)
    ·
      refine ⟨14038073339115279993631537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18717431118820373324842049 14038073339115279993631537)
      ·
        refine ⟨10528555004336459995223653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14038073339115279993631537 10528555004336459995223653)
        ·
          refine ⟨1974104063313086249104435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10528555004336459995223653 1974104063313086249104435)
          ·
            refine ⟨2961156094969629373656653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974104063313086249104435 2961156094969629373656653)
            ·
              refine ⟨1110433535613611015121245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2961156094969629373656653 1110433535613611015121245)
              ·
                refine ⟨416412575855104130670467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110433535613611015121245 416412575855104130670467)
                ·
                  refine ⟨624618863782656196005701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416412575855104130670467 624618863782656196005701)
                  ·
                    refine ⟨117116036959248036751069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624618863782656196005701 117116036959248036751069)
                    ·
                      rfl

theorem cell23_684248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_684248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684248 prefixEnd_684248 := by exact prefixLift 684248
  have htrace : WordTrace (prefixWord ++ tailWord_684248) baseStart_684248 baseEnd_684248 := by
    simpa [prefixWord, tailWord_684248, baseEnd_684248] using wordTrace_append hprefix tailTrace_684248
  have hstable : (prefixWord ++ tailWord_684248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684248).length < 2 ^ (prefixWord ++ tailWord_684248).sum := by decide
  have hdescent : baseEnd_684248 < baseStart_684248 := by decide
  rcases family_descends (prefixWord ++ tailWord_684248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684321 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_684321 : Nat := 118140960795 + 684321 * 2 ^ 59
def prefixEnd_684321 : Nat := 4983230072969 + 3 ^ 40 * 684321 * 2
def baseEnd_684321 : Nat := 117128531655174108213457

theorem tailTrace_684321 : CollatzResearch.WordTrace tailWord_684321 prefixEnd_684321 117128531655174108213457 := by
  unfold tailWord_684321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24959237353829364567196817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16639491569219576378131211 24959237353829364567196817)
  ·
    refine ⟨18719428015372023425397613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24959237353829364567196817 18719428015372023425397613)
    ·
      refine ⟨7019785505764508784524105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18719428015372023425397613 7019785505764508784524105)
      ·
        refine ⟨5264839129323381588393079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7019785505764508784524105 5264839129323381588393079)
        ·
          refine ⟨7897258693985072382589619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264839129323381588393079 7897258693985072382589619)
          ·
            refine ⟨11845888040977608573884429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897258693985072382589619 11845888040977608573884429)
            ·
              refine ⟨4442208015366603215206661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11845888040977608573884429 4442208015366603215206661)
              ·
                refine ⟨832914002881238102851249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4442208015366603215206661 832914002881238102851249)
                ·
                  refine ⟨624685502160928577138437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 832914002881238102851249 624685502160928577138437)
                  ·
                    refine ⟨117128531655174108213457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624685502160928577138437 117128531655174108213457)
                    ·
                      rfl

theorem cell23_684321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_684321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684321 prefixEnd_684321 := by exact prefixLift 684321
  have htrace : WordTrace (prefixWord ++ tailWord_684321) baseStart_684321 baseEnd_684321 := by
    simpa [prefixWord, tailWord_684321, baseEnd_684321] using wordTrace_append hprefix tailTrace_684321
  have hstable : (prefixWord ++ tailWord_684321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684321).length < 2 ^ (prefixWord ++ tailWord_684321).sum := by decide
  have hdescent : baseEnd_684321 < baseStart_684321 := by decide
  rcases family_descends (prefixWord ++ tailWord_684321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684322 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_684322 : Nat := 118140960795 + 684322 * 2 ^ 59
def prefixEnd_684322 : Nat := 4983230072969 + 3 ^ 40 * 684322 * 2
def baseEnd_684322 : Nat := 351386108446176820727867

theorem tailTrace_684322 : CollatzResearch.WordTrace tailWord_684322 prefixEnd_684322 351386108446176820727867 := by
  unfold tailWord_684322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239818456706435434495805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16639515884550494491988813 6239818456706435434495805)
  ·
    refine ⟨2339931921264913287935927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6239818456706435434495805 2339931921264913287935927)
    ·
      refine ⟨3509897881897369931903891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339931921264913287935927 3509897881897369931903891)
      ·
        refine ⟨5264846822846054897855837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509897881897369931903891 5264846822846054897855837)
        ·
          refine ⟨1974317558567270586695939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5264846822846054897855837 1974317558567270586695939)
          ·
            refine ⟨2961476337850905880043909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974317558567270586695939 2961476337850905880043909)
            ·
              refine ⟨555276813347044852508233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2961476337850905880043909 555276813347044852508233)
              ·
                refine ⟨416457610010283639381175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555276813347044852508233 416457610010283639381175)
                ·
                  refine ⟨624686415015425459071763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416457610010283639381175 624686415015425459071763)
                  ·
                    refine ⟨937029622523138188607645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 624686415015425459071763 937029622523138188607645)
                    ·
                      refine ⟨351386108446176820727867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937029622523138188607645 351386108446176820727867)
                      ·
                        rfl

theorem cell23_684322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_684322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684322 prefixEnd_684322 := by exact prefixLift 684322
  have htrace : WordTrace (prefixWord ++ tailWord_684322) baseStart_684322 baseEnd_684322 := by
    simpa [prefixWord, tailWord_684322, baseEnd_684322] using wordTrace_append hprefix tailTrace_684322
  have hstable : (prefixWord ++ tailWord_684322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684322).length < 2 ^ (prefixWord ++ tailWord_684322).sum := by decide
  have hdescent : baseEnd_684322 < baseStart_684322 := by decide
  rcases family_descends (prefixWord ++ tailWord_684322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684341 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_684341 : Nat := 118140960795 + 684341 * 2 ^ 59
def prefixEnd_684341 : Nat := 4983230072969 + 3 ^ 40 * 684341 * 2
def baseEnd_684341 : Nat := 351395864578612246390279

theorem tailTrace_684341 : CollatzResearch.WordTrace tailWord_684341 prefixEnd_684341 351395864578612246390279 := by
  unfold tailWord_684341
  simp only [CollatzResearch.WordTrace]
  refine ⟨24959966813756907982924877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16639977875837938655283251 24959966813756907982924877)
  ·
    refine ⟨9359987555158840493596829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24959966813756907982924877 9359987555158840493596829)
    ·
      refine ⟨3509995333184565185098811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9359987555158840493596829 3509995333184565185098811)
      ·
        refine ⟨5264992999776847777648217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509995333184565185098811 5264992999776847777648217)
        ·
          refine ⟨3948744749832635833236163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5264992999776847777648217 3948744749832635833236163)
          ·
            refine ⟨5923117124748953749854245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948744749832635833236163 5923117124748953749854245)
            ·
              refine ⟨1110584460890428828097671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5923117124748953749854245 1110584460890428828097671)
              ·
                refine ⟨1665876691335643242146507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110584460890428828097671 1665876691335643242146507)
                ·
                  refine ⟨2498815037003464863219761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665876691335643242146507 2498815037003464863219761)
                  ·
                    refine ⟨1874111277752598647414821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2498815037003464863219761 1874111277752598647414821)
                    ·
                      refine ⟨351395864578612246390279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1874111277752598647414821 351395864578612246390279)
                      ·
                        rfl

theorem cell23_684341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_684341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684341 prefixEnd_684341 := by exact prefixLift 684341
  have htrace : WordTrace (prefixWord ++ tailWord_684341) baseStart_684341 baseEnd_684341 := by
    simpa [prefixWord, tailWord_684341, baseEnd_684341] using wordTrace_append hprefix tailTrace_684341
  have hstable : (prefixWord ++ tailWord_684341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684341).length < 2 ^ (prefixWord ++ tailWord_684341).sum := by decide
  have hdescent : baseEnd_684341 < baseStart_684341 := by decide
  rcases family_descends (prefixWord ++ tailWord_684341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684345 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 3, 2, 2]
def baseStart_684345 : Nat := 118140960795 + 684345 * 2 ^ 59
def prefixEnd_684345 : Nat := 4983230072969 + 3 ^ 40 * 684345 * 2
def baseEnd_684345 : Nat := 351397918501230230740261

theorem tailTrace_684345 : CollatzResearch.WordTrace tailWord_684345 prefixEnd_684345 351397918501230230740261 := by
  unfold tailWord_684345
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960112705742416666070489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16640075137161611110713659 24960112705742416666070489)
  ·
    refine ⟨18720084529306812499552867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24960112705742416666070489 18720084529306812499552867)
    ·
      refine ⟨28080126793960218749329301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18720084529306812499552867 28080126793960218749329301)
      ·
        refine ⟨1316255943466885253874811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28080126793960218749329301 1316255943466885253874811)
        ·
          refine ⟨1974383915200327880812217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316255943466885253874811 1974383915200327880812217)
          ·
            refine ⟨1480787936400245910609163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974383915200327880812217 1480787936400245910609163)
            ·
              refine ⟨2221181904600368865913745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480787936400245910609163 2221181904600368865913745)
              ·
                refine ⟨1665886428450276649435309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221181904600368865913745 1665886428450276649435309)
                ·
                  refine ⟨624707410668853743538241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1665886428450276649435309 624707410668853743538241)
                  ·
                    refine ⟨468530558001640307653681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624707410668853743538241 468530558001640307653681)
                    ·
                      refine ⟨351397918501230230740261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468530558001640307653681 351397918501230230740261)
                      ·
                        rfl

theorem cell23_684345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_684345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684345 prefixEnd_684345 := by exact prefixLift 684345
  have htrace : WordTrace (prefixWord ++ tailWord_684345) baseStart_684345 baseEnd_684345 := by
    simpa [prefixWord, tailWord_684345, baseEnd_684345] using wordTrace_append hprefix tailTrace_684345
  have hstable : (prefixWord ++ tailWord_684345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684345).length < 2 ^ (prefixWord ++ tailWord_684345).sum := by decide
  have hdescent : baseEnd_684345 < baseStart_684345 := by decide
  rcases family_descends (prefixWord ++ tailWord_684345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684361 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 3]
def baseStart_684361 : Nat := 118140960795 + 684361 * 2 ^ 59
def prefixEnd_684361 : Nat := 4983230072969 + 3 ^ 40 * 684361 * 2
def baseEnd_684361 : Nat := 351406134191702168140187

theorem tailTrace_684361 : CollatzResearch.WordTrace tailWord_684361 prefixEnd_684361 351406134191702168140187 := by
  unfold tailWord_684361
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960696273684451398652937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16640464182456300932435291 24960696273684451398652937)
  ·
    refine ⟨18720522205263338548989703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24960696273684451398652937 18720522205263338548989703)
    ·
      refine ⟨28080783307895007823484555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18720522205263338548989703 28080783307895007823484555)
      ·
        refine ⟨42121174961842511735226833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28080783307895007823484555 42121174961842511735226833)
        ·
          refine ⟨31590881221381883801420125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42121174961842511735226833 31590881221381883801420125)
          ·
            refine ⟨11846580458018206425532547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31590881221381883801420125 11846580458018206425532547)
            ·
              refine ⟨17769870687027309638298821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11846580458018206425532547 17769870687027309638298821)
              ·
                refine ⟨3331850753817620557181029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17769870687027309638298821 3331850753817620557181029)
                ·
                  refine ⟨624722016340803854471443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3331850753817620557181029 624722016340803854471443)
                  ·
                    refine ⟨937083024511205781707165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 624722016340803854471443 937083024511205781707165)
                    ·
                      refine ⟨351406134191702168140187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937083024511205781707165 351406134191702168140187)
                      ·
                        rfl

theorem cell23_684361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_684361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684361 prefixEnd_684361 := by exact prefixLift 684361
  have htrace : WordTrace (prefixWord ++ tailWord_684361) baseStart_684361 baseEnd_684361 := by
    simpa [prefixWord, tailWord_684361, baseEnd_684361] using wordTrace_append hprefix tailTrace_684361
  have hstable : (prefixWord ++ tailWord_684361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684361).length < 2 ^ (prefixWord ++ tailWord_684361).sum := by decide
  have hdescent : baseEnd_684361 < baseStart_684361 := by decide
  rcases family_descends (prefixWord ++ tailWord_684361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684371 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 5, 3, 2]
def baseStart_684371 : Nat := 118140960795 + 684371 * 2 ^ 59
def prefixEnd_684371 : Nat := 4983230072969 + 3 ^ 40 * 684371 * 2
def baseEnd_684371 : Nat := 351411268998247129015141

theorem tailTrace_684371 : CollatzResearch.WordTrace tailWord_684371 prefixEnd_684371 351411268998247129015141 := by
  unfold tailWord_684371
  simp only [CollatzResearch.WordTrace]
  refine ⟨24961061003648223106516967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16640707335765482071011311 24961061003648223106516967)
  ·
    refine ⟨37441591505472334659775451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24961061003648223106516967 37441591505472334659775451)
    ·
      refine ⟨56162387258208501989663177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37441591505472334659775451 56162387258208501989663177)
      ·
        refine ⟨42121790443656376492247383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56162387258208501989663177 42121790443656376492247383)
        ·
          refine ⟨63182685665484564738371075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42121790443656376492247383 63182685665484564738371075)
          ·
            refine ⟨94774028498226847107556613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63182685665484564738371075 94774028498226847107556613)
            ·
              refine ⟨17770130343417533832666865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94774028498226847107556613 17770130343417533832666865)
              ·
                refine ⟨13327597757563150374500149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17770130343417533832666865 13327597757563150374500149)
                ·
                  refine ⟨1249462289771545347609389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13327597757563150374500149 1249462289771545347609389)
                  ·
                    refine ⟨468548358664329505353521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249462289771545347609389 468548358664329505353521)
                    ·
                      refine ⟨351411268998247129015141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468548358664329505353521 351411268998247129015141)
                      ·
                        rfl

theorem cell23_684371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3, 2].length) (baseStart_684371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684371 prefixEnd_684371 := by exact prefixLift 684371
  have htrace : WordTrace (prefixWord ++ tailWord_684371) baseStart_684371 baseEnd_684371 := by
    simpa [prefixWord, tailWord_684371, baseEnd_684371] using wordTrace_append hprefix tailTrace_684371
  have hstable : (prefixWord ++ tailWord_684371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684371).length < 2 ^ (prefixWord ++ tailWord_684371).sum := by decide
  have hdescent : baseEnd_684371 < baseStart_684371 := by decide
  rcases family_descends (prefixWord ++ tailWord_684371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684405 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_684405 : Nat := 118140960795 + 684405 * 2 ^ 59
def prefixEnd_684405 : Nat := 4983230072969 + 3 ^ 40 * 684405 * 2
def baseEnd_684405 : Nat := 351428727340499995989985

theorem tailTrace_684405 : CollatzResearch.WordTrace tailWord_684405 prefixEnd_684405 351428727340499995989985 := by
  unfold tailWord_684405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24962301085525046913254669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16641534057016697942169779 24962301085525046913254669)
  ·
    refine ⟨9360862907071892592470501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24962301085525046913254669 9360862907071892592470501)
    ·
      refine ⟨1755161795075979861088219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9360862907071892592470501 1755161795075979861088219)
      ·
        refine ⟨2632742692613969791632329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755161795075979861088219 2632742692613969791632329)
        ·
          refine ⟨1974557019460477343724247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632742692613969791632329 1974557019460477343724247)
          ·
            refine ⟨2961835529190716015586371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974557019460477343724247 2961835529190716015586371)
            ·
              refine ⟨4442753293786074023379557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961835529190716015586371 4442753293786074023379557)
              ·
                refine ⟨833016242584888879383667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4442753293786074023379557 833016242584888879383667)
                ·
                  refine ⟨1249524363877333319075501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833016242584888879383667 1249524363877333319075501)
                  ·
                    refine ⟨468571636453999994653313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1249524363877333319075501 468571636453999994653313)
                    ·
                      refine ⟨351428727340499995989985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468571636453999994653313 351428727340499995989985)
                      ·
                        rfl

theorem cell23_684405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_684405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684405 prefixEnd_684405 := by exact prefixLift 684405
  have htrace : WordTrace (prefixWord ++ tailWord_684405) baseStart_684405 baseEnd_684405 := by
    simpa [prefixWord, tailWord_684405, baseEnd_684405] using wordTrace_append hprefix tailTrace_684405
  have hstable : (prefixWord ++ tailWord_684405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684405).length < 2 ^ (prefixWord ++ tailWord_684405).sum := by decide
  have hdescent : baseEnd_684405 < baseStart_684405 := by decide
  rcases family_descends (prefixWord ++ tailWord_684405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684452 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_684452 : Nat := 118140960795 + 684452 * 2 ^ 59
def prefixEnd_684452 : Nat := 4983230072969 + 3 ^ 40 * 684452 * 2
def baseEnd_684452 : Nat := 351452860931261312102269

theorem tailTrace_684452 : CollatzResearch.WordTrace tailWord_684452 prefixEnd_684452 351452860931261312102269 := by
  unfold tailWord_684452
  simp only [CollatzResearch.WordTrace]
  refine ⟨12482007658177386970107805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16642676877569849293477073 12482007658177386970107805)
  ·
    refine ⟨4680752871816520113790427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12482007658177386970107805 4680752871816520113790427)
    ·
      refine ⟨7021129307724780170685641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4680752871816520113790427 7021129307724780170685641)
      ·
        refine ⟨5265846980793585128014231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7021129307724780170685641 5265846980793585128014231)
        ·
          refine ⟨7898770471190377692021347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265846980793585128014231 7898770471190377692021347)
          ·
            refine ⟨11848155706785566538032021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898770471190377692021347 11848155706785566538032021)
            ·
              refine ⟨555382298755573431470251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11848155706785566538032021 555382298755573431470251)
              ·
                refine ⟨833073448133360147205377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555382298755573431470251 833073448133360147205377)
                ·
                  refine ⟨624805086100020110404033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833073448133360147205377 624805086100020110404033)
                  ·
                    refine ⟨468603814575015082803025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624805086100020110404033 468603814575015082803025)
                    ·
                      refine ⟨351452860931261312102269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468603814575015082803025 351452860931261312102269)
                      ·
                        rfl

theorem cell23_684452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_684452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684452 prefixEnd_684452 := by exact prefixLift 684452
  have htrace : WordTrace (prefixWord ++ tailWord_684452) baseStart_684452 baseEnd_684452 := by
    simpa [prefixWord, tailWord_684452, baseEnd_684452] using wordTrace_append hprefix tailTrace_684452
  have hstable : (prefixWord ++ tailWord_684452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684452).length < 2 ^ (prefixWord ++ tailWord_684452).sum := by decide
  have hdescent : baseEnd_684452 < baseStart_684452 := by decide
  rcases family_descends (prefixWord ++ tailWord_684452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684471 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 2, 5]
def baseStart_684471 : Nat := 118140960795 + 684471 * 2 ^ 59
def prefixEnd_684471 : Nat := 4983230072969 + 3 ^ 40 * 684471 * 2
def baseEnd_684471 : Nat := 117154205687898912588227

theorem tailTrace_684471 : CollatzResearch.WordTrace tailWord_684471 prefixEnd_684471 117154205687898912588227 := by
  unfold tailWord_684471
  simp only [CollatzResearch.WordTrace]
  refine ⟨24964708303285940185157267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16643138868857293456771511 24964708303285940185157267)
  ·
    refine ⟨37447062454928910277735901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24964708303285940185157267 37447062454928910277735901)
    ·
      refine ⟨14042648420598341354150963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37447062454928910277735901 14042648420598341354150963)
      ·
        refine ⟨21063972630897512031226445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14042648420598341354150963 21063972630897512031226445)
        ·
          refine ⟨7898989736586567011709917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21063972630897512031226445 7898989736586567011709917)
          ·
            refine ⟨2962121151219962629391219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7898989736586567011709917 2962121151219962629391219)
            ·
              refine ⟨4443181726829943944086829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962121151219962629391219 4443181726829943944086829)
              ·
                refine ⟨1666193147561228979032561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4443181726829943944086829 1666193147561228979032561)
                ·
                  refine ⟨1249644860670921734274421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1666193147561228979032561 1249644860670921734274421)
                  ·
                    refine ⟨117154205687898912588227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1249644860670921734274421 117154205687898912588227)
                    ·
                      rfl

theorem cell23_684471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_684471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684471 prefixEnd_684471 := by exact prefixLift 684471
  have htrace : WordTrace (prefixWord ++ tailWord_684471) baseStart_684471 baseEnd_684471 := by
    simpa [prefixWord, tailWord_684471, baseEnd_684471] using wordTrace_append hprefix tailTrace_684471
  have hstable : (prefixWord ++ tailWord_684471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684471).length < 2 ^ (prefixWord ++ tailWord_684471).sum := by decide
  have hdescent : baseEnd_684471 < baseStart_684471 := by decide
  rcases family_descends (prefixWord ++ tailWord_684471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684492 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 5]
def baseStart_684492 : Nat := 118140960795 + 684492 * 2 ^ 59
def prefixEnd_684492 : Nat := 4983230072969 + 3 ^ 40 * 684492 * 2
def baseEnd_684492 : Nat := 39052600017493461733565

theorem tailTrace_684492 : CollatzResearch.WordTrace tailWord_684492 prefixEnd_684492 39052600017493461733565 := by
  unfold tailWord_684492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12482737118104930385835865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16643649490806573847781153 12482737118104930385835865)
  ·
    refine ⟨9362052838578697789376899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12482737118104930385835865 9362052838578697789376899)
    ·
      refine ⟨14043079257868046684065349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9362052838578697789376899 14043079257868046684065349)
      ·
        refine ⟨2633077360850258753262253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14043079257868046684065349 2633077360850258753262253)
        ·
          refine ⟨987404010318847032473345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633077360850258753262253 987404010318847032473345)
          ·
            refine ⟨740553007739135274355009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987404010318847032473345 740553007739135274355009)
            ·
              refine ⟨555414755804351455766257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740553007739135274355009 555414755804351455766257)
              ·
                refine ⟨416561066853263591824693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555414755804351455766257 416561066853263591824693)
                ·
                  refine ⟨39052600017493461733565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416561066853263591824693 39052600017493461733565)
                  ·
                    rfl

theorem cell23_684492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_684492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684492 prefixEnd_684492 := by exact prefixLift 684492
  have htrace : WordTrace (prefixWord ++ tailWord_684492) baseStart_684492 baseEnd_684492 := by
    simpa [prefixWord, tailWord_684492, baseEnd_684492] using wordTrace_append hprefix tailTrace_684492
  have hstable : (prefixWord ++ tailWord_684492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684492).length < 2 ^ (prefixWord ++ tailWord_684492).sum := by decide
  have hdescent : baseEnd_684492 < baseStart_684492 := by decide
  rcases family_descends (prefixWord ++ tailWord_684492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684525 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_684525 : Nat := 118140960795 + 684525 * 2 ^ 59
def prefixEnd_684525 : Nat := 4983230072969 + 3 ^ 40 * 684525 * 2
def baseEnd_684525 : Nat := 351490345019039526489433

theorem tailTrace_684525 : CollatzResearch.WordTrace tailWord_684525 prefixEnd_684525 351490345019039526489433 := by
  unfold tailWord_684525
  simp only [CollatzResearch.WordTrace]
  refine ⟨24966677845090307407623029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16644451896726871605082019 24966677845090307407623029)
  ·
    refine ⟨2340626047977216319464659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24966677845090307407623029 2340626047977216319464659)
    ·
      refine ⟨3510939071965824479196989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340626047977216319464659 3510939071965824479196989)
      ·
        refine ⟨1316602151987184179698871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3510939071965824479196989 1316602151987184179698871)
        ·
          refine ⟨1974903227980776269548307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316602151987184179698871 1974903227980776269548307)
          ·
            refine ⟨2962354841971164404322461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974903227980776269548307 2962354841971164404322461)
            ·
              refine ⟨1110883065739186651620923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2962354841971164404322461 1110883065739186651620923)
              ·
                refine ⟨1666324598608779977431385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110883065739186651620923 1666324598608779977431385)
                ·
                  refine ⟨1249743448956584983073539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1666324598608779977431385 1249743448956584983073539)
                  ·
                    refine ⟨1874615173434877474610309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1249743448956584983073539 1874615173434877474610309)
                    ·
                      refine ⟨351490345019039526489433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1874615173434877474610309 351490345019039526489433)
                      ·
                        rfl

theorem cell23_684525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_684525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684525 prefixEnd_684525 := by exact prefixLift 684525
  have htrace : WordTrace (prefixWord ++ tailWord_684525) baseStart_684525 baseEnd_684525 := by
    simpa [prefixWord, tailWord_684525, baseEnd_684525] using wordTrace_append hprefix tailTrace_684525
  have hstable : (prefixWord ++ tailWord_684525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684525).length < 2 ^ (prefixWord ++ tailWord_684525).sum := by decide
  have hdescent : baseEnd_684525 < baseStart_684525 := by decide
  rcases family_descends (prefixWord ++ tailWord_684525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684548 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 8]
def baseStart_684548 : Nat := 118140960795 + 684548 * 2 ^ 59
def prefixEnd_684548 : Nat := 4983230072969 + 3 ^ 40 * 684548 * 2
def baseEnd_684548 : Nat := 39055795008232548500203

theorem tailTrace_684548 : CollatzResearch.WordTrace tailWord_684548 prefixEnd_684548 39055795008232548500203 := by
  unfold tailWord_684548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483758362003491167855149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16645011149337988223806865 12483758362003491167855149)
  ·
    refine ⟨4681409385751309187945681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12483758362003491167855149 4681409385751309187945681)
    ·
      refine ⟨3511057039313481890959261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4681409385751309187945681 3511057039313481890959261)
      ·
        refine ⟨1316646389742555709109723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3511057039313481890959261 1316646389742555709109723)
        ·
          refine ⟨1974969584613833563664585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316646389742555709109723 1974969584613833563664585)
          ·
            refine ⟨1481227188460375172748439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974969584613833563664585 1481227188460375172748439)
            ·
              refine ⟨2221840782690562759122659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481227188460375172748439 2221840782690562759122659)
              ·
                refine ⟨3332761174035844138683989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221840782690562759122659 3332761174035844138683989)
                ·
                  refine ⟨39055795008232548500203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3332761174035844138683989 39055795008232548500203)
                  ·
                    rfl

theorem cell23_684548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_684548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684548 prefixEnd_684548 := by exact prefixLift 684548
  have htrace : WordTrace (prefixWord ++ tailWord_684548) baseStart_684548 baseEnd_684548 := by
    simpa [prefixWord, tailWord_684548, baseEnd_684548] using wordTrace_append hprefix tailTrace_684548
  have hstable : (prefixWord ++ tailWord_684548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684548).length < 2 ^ (prefixWord ++ tailWord_684548).sum := by decide
  have hdescent : baseEnd_684548 < baseStart_684548 := by decide
  rcases family_descends (prefixWord ++ tailWord_684548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684561 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_684561 : Nat := 118140960795 + 684561 * 2 ^ 59
def prefixEnd_684561 : Nat := 4983230072969 + 3 ^ 40 * 684561 * 2
def baseEnd_684561 : Nat := 117169610107533795213089

theorem tailTrace_684561 : CollatzResearch.WordTrace tailWord_684561 prefixEnd_684561 117169610107533795213089 := by
  unfold tailWord_684561
  simp only [CollatzResearch.WordTrace]
  refine ⟨24967990872959885555933537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16645327248639923703955691 24967990872959885555933537)
  ·
    refine ⟨18725993154719914166950153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24967990872959885555933537 18725993154719914166950153)
    ·
      refine ⟨14044494866039935625212615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18725993154719914166950153 14044494866039935625212615)
      ·
        refine ⟨21066742299059903437818923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14044494866039935625212615 21066742299059903437818923)
        ·
          refine ⟨31600113448589855156728385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21066742299059903437818923 31600113448589855156728385)
          ·
            refine ⟨23700085086442391367546289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31600113448589855156728385 23700085086442391367546289)
            ·
              refine ⟨17775063814831793525659717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23700085086442391367546289 17775063814831793525659717)
              ·
                refine ⟨3332824465280961286061197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17775063814831793525659717 3332824465280961286061197)
                ·
                  refine ⟨1249809174480360482272949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3332824465280961286061197 1249809174480360482272949)
                  ·
                    refine ⟨117169610107533795213089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1249809174480360482272949 117169610107533795213089)
                    ·
                      rfl

theorem cell23_684561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_684561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684561 prefixEnd_684561 := by exact prefixLift 684561
  have htrace : WordTrace (prefixWord ++ tailWord_684561) baseStart_684561 baseEnd_684561 := by
    simpa [prefixWord, tailWord_684561, baseEnd_684561] using wordTrace_append hprefix tailTrace_684561
  have hstable : (prefixWord ++ tailWord_684561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684561).length < 2 ^ (prefixWord ++ tailWord_684561).sum := by decide
  have hdescent : baseEnd_684561 < baseStart_684561 := by decide
  rcases family_descends (prefixWord ++ tailWord_684561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684592 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 1, 1, 3]
def baseStart_684592 : Nat := 118140960795 + 684592 * 2 ^ 59
def prefixEnd_684592 : Nat := 4983230072969 + 3 ^ 40 * 684592 * 2
def baseEnd_684592 : Nat := 351524748222890764351625

theorem tailTrace_684592 : CollatzResearch.WordTrace tailWord_684592 prefixEnd_684592 351524748222890764351625 := by
  unfold tailWord_684592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484560767923788925156015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16646081023898385233541353 12484560767923788925156015)
  ·
    refine ⟨18726841151885683387734023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12484560767923788925156015 18726841151885683387734023)
    ·
      refine ⟨28090261727828525081601035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18726841151885683387734023 28090261727828525081601035)
      ·
        refine ⟨42135392591742787622401553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28090261727828525081601035 42135392591742787622401553)
        ·
          refine ⟨31601544443807090716801165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42135392591742787622401553 31601544443807090716801165)
          ·
            refine ⟨11850579166427659018800437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31601544443807090716801165 11850579166427659018800437)
            ·
              refine ⟨1110991796852593033012541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11850579166427659018800437 1110991796852593033012541)
              ·
                refine ⟨416621923819722387379703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110991796852593033012541 416621923819722387379703)
                ·
                  refine ⟨624932885729583581069555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416621923819722387379703 624932885729583581069555)
                  ·
                    refine ⟨937399328594375371604333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 624932885729583581069555 937399328594375371604333)
                    ·
                      refine ⟨351524748222890764351625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937399328594375371604333 351524748222890764351625)
                      ·
                        rfl

theorem cell23_684592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 1, 3].length) (baseStart_684592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684592 prefixEnd_684592 := by exact prefixLift 684592
  have htrace : WordTrace (prefixWord ++ tailWord_684592) baseStart_684592 baseEnd_684592 := by
    simpa [prefixWord, tailWord_684592, baseEnd_684592] using wordTrace_append hprefix tailTrace_684592
  have hstable : (prefixWord ++ tailWord_684592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684592).length < 2 ^ (prefixWord ++ tailWord_684592).sum := by decide
  have hdescent : baseEnd_684592 < baseStart_684592 := by decide
  rcases family_descends (prefixWord ++ tailWord_684592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684608 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_684608 : Nat := 118140960795 + 684608 * 2 ^ 59
def prefixEnd_684608 : Nat := 4983230072969 + 3 ^ 40 * 684608 * 2
def baseEnd_684608 : Nat := 117177654637787567250517

theorem tailTrace_684608 : CollatzResearch.WordTrace tailWord_684608 prefixEnd_684608 117177654637787567250517 := by
  unfold tailWord_684608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484852551894806291447239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16646470069193075055262985 12484852551894806291447239)
  ·
    refine ⟨18727278827842209437170859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12484852551894806291447239 18727278827842209437170859)
    ·
      refine ⟨28090918241763314155756289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18727278827842209437170859 28090918241763314155756289)
      ·
        refine ⟨21068188681322485616817217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28090918241763314155756289 21068188681322485616817217)
        ·
          refine ⟨15801141510991864212612913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21068188681322485616817217 15801141510991864212612913)
          ·
            refine ⟨11850856133243898159459685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15801141510991864212612913 11850856133243898159459685)
            ·
              refine ⟨2222035524983230904898691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11850856133243898159459685 2222035524983230904898691)
              ·
                refine ⟨3333053287474846357348037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222035524983230904898691 3333053287474846357348037)
                ·
                  refine ⟨624947491401533692002757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3333053287474846357348037 624947491401533692002757)
                  ·
                    refine ⟨117177654637787567250517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624947491401533692002757 117177654637787567250517)
                    ·
                      rfl

theorem cell23_684608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_684608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684608 prefixEnd_684608 := by exact prefixLift 684608
  have htrace : WordTrace (prefixWord ++ tailWord_684608) baseStart_684608 baseEnd_684608 := by
    simpa [prefixWord, tailWord_684608, baseEnd_684608] using wordTrace_append hprefix tailTrace_684608
  have hstable : (prefixWord ++ tailWord_684608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684608).length < 2 ^ (prefixWord ++ tailWord_684608).sum := by decide
  have hdescent : baseEnd_684608 < baseStart_684608 := by decide
  rcases family_descends (prefixWord ++ tailWord_684608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684618 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_684618 : Nat := 118140960795 + 684618 * 2 ^ 59
def prefixEnd_684618 : Nat := 4983230072969 + 3 ^ 40 * 684618 * 2
def baseEnd_684618 : Nat := 351538098719907662626505

theorem tailTrace_684618 : CollatzResearch.WordTrace tailWord_684618 prefixEnd_684618 351538098719907662626505 := by
  unfold tailWord_684618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6242517458438346072689627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16646713222502256193839005 6242517458438346072689627)
  ·
    refine ⟨9363776187657519109034441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6242517458438346072689627 9363776187657519109034441)
    ·
      refine ⟨7022832140743139331775831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9363776187657519109034441 7022832140743139331775831)
      ·
        refine ⟨10534248211114708997663747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7022832140743139331775831 10534248211114708997663747)
        ·
          refine ⟨15801372316672063496495621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534248211114708997663747 15801372316672063496495621)
          ·
            refine ⟨2962757309376011905592929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15801372316672063496495621 2962757309376011905592929)
            ·
              refine ⟨2222067982032008929194697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962757309376011905592929 2222067982032008929194697)
              ·
                refine ⟨1666550986524006696896023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222067982032008929194697 1666550986524006696896023)
                ·
                  refine ⟨2499826479786010045344035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666550986524006696896023 2499826479786010045344035)
                  ·
                    refine ⟨3749739719679015068016053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2499826479786010045344035 3749739719679015068016053)
                    ·
                      refine ⟨351538098719907662626505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3749739719679015068016053 351538098719907662626505)
                      ·
                        rfl

theorem cell23_684618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_684618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684618 prefixEnd_684618 := by exact prefixLift 684618
  have htrace : WordTrace (prefixWord ++ tailWord_684618) baseStart_684618 baseEnd_684618 := by
    simpa [prefixWord, tailWord_684618, baseEnd_684618] using wordTrace_append hprefix tailTrace_684618
  have hstable : (prefixWord ++ tailWord_684618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684618).length < 2 ^ (prefixWord ++ tailWord_684618).sum := by decide
  have hdescent : baseEnd_684618 < baseStart_684618 := by decide
  rcases family_descends (prefixWord ++ tailWord_684618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684625 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_684625 : Nat := 118140960795 + 684625 * 2 ^ 59
def prefixEnd_684625 : Nat := 4983230072969 + 3 ^ 40 * 684625 * 2
def baseEnd_684625 : Nat := 117180564361496378412991

theorem tailTrace_684625 : CollatzResearch.WordTrace tailWord_684625 prefixEnd_684625 117180564361496378412991 := by
  unfold tailWord_684625
  simp only [CollatzResearch.WordTrace]
  refine ⟨24970325144728024486263329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16646883429818682990842219 24970325144728024486263329)
  ·
    refine ⟨18727743858546018364697497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24970325144728024486263329 18727743858546018364697497)
    ·
      refine ⟨14045807893909513773523123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18727743858546018364697497 14045807893909513773523123)
      ·
        refine ⟨21068711840864270660284685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14045807893909513773523123 21068711840864270660284685)
        ·
          refine ⟨7900766940324101497606757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21068711840864270660284685 7900766940324101497606757)
          ·
            refine ⟨1481393801310769030801267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7900766940324101497606757 1481393801310769030801267)
            ·
              refine ⟨2222090701966153546201901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481393801310769030801267 2222090701966153546201901)
              ·
                refine ⟨833284013237307579825713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222090701966153546201901 833284013237307579825713)
                ·
                  refine ⟨624963009927980684869285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833284013237307579825713 624963009927980684869285)
                  ·
                    refine ⟨117180564361496378412991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624963009927980684869285 117180564361496378412991)
                    ·
                      rfl

theorem cell23_684625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_684625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684625 prefixEnd_684625 := by exact prefixLift 684625
  have htrace : WordTrace (prefixWord ++ tailWord_684625) baseStart_684625 baseEnd_684625 := by
    simpa [prefixWord, tailWord_684625, baseEnd_684625] using wordTrace_append hprefix tailTrace_684625
  have hstable : (prefixWord ++ tailWord_684625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684625).length < 2 ^ (prefixWord ++ tailWord_684625).sum := by decide
  have hdescent : baseEnd_684625 < baseStart_684625 := by decide
  rcases family_descends (prefixWord ++ tailWord_684625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684628 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_684628 : Nat := 118140960795 + 684628 * 2 ^ 59
def prefixEnd_684628 : Nat := 4983230072969 + 3 ^ 40 * 684628 * 2
def baseEnd_684628 : Nat := 351543233526452623501459

theorem tailTrace_684628 : CollatzResearch.WordTrace tailWord_684628 prefixEnd_684628 351543233526452623501459 := by
  unfold tailWord_684628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12485217281858577999311269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16646956375811437332415025 12485217281858577999311269)
  ·
    refine ⟨2340978240348483374870863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12485217281858577999311269 2340978240348483374870863)
    ·
      refine ⟨3511467360522725062306295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340978240348483374870863 3511467360522725062306295)
      ·
        refine ⟨5267201040784087593459443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511467360522725062306295 5267201040784087593459443)
        ·
          refine ⟨7900801561176131390189165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267201040784087593459443 7900801561176131390189165)
          ·
            refine ⟨2962800585441049271320937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7900801561176131390189165 2962800585441049271320937)
            ·
              refine ⟨2222100439080786953490703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2962800585441049271320937 2222100439080786953490703)
              ·
                refine ⟨3333150658621180430236055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222100439080786953490703 3333150658621180430236055)
                ·
                  refine ⟨4999725987931770645354083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333150658621180430236055 4999725987931770645354083)
                  ·
                    refine ⟨7499588981897655968031125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4999725987931770645354083 7499588981897655968031125)
                    ·
                      refine ⟨351543233526452623501459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7499588981897655968031125 351543233526452623501459)
                      ·
                        rfl

theorem cell23_684628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_684628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684628 prefixEnd_684628 := by exact prefixLift 684628
  have htrace : WordTrace (prefixWord ++ tailWord_684628) baseStart_684628 baseEnd_684628 := by
    simpa [prefixWord, tailWord_684628, baseEnd_684628] using wordTrace_append hprefix tailTrace_684628
  have hstable : (prefixWord ++ tailWord_684628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684628).length < 2 ^ (prefixWord ++ tailWord_684628).sum := by decide
  have hdescent : baseEnd_684628 < baseStart_684628 := by decide
  rcases family_descends (prefixWord ++ tailWord_684628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684642 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_684642 : Nat := 118140960795 + 684642 * 2 ^ 59
def prefixEnd_684642 : Nat := 4983230072969 + 3 ^ 40 * 684642 * 2
def baseEnd_684642 : Nat := 117183474085205189575465

theorem tailTrace_684642 : CollatzResearch.WordTrace tailWord_684642 prefixEnd_684642 117183474085205189575465 := by
  unfold tailWord_684642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6242736296416609097408045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16647296790444290926421453 6242736296416609097408045)
  ·
    refine ⟨2341026111156228411528017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6242736296416609097408045 2341026111156228411528017)
    ·
      refine ⟨1755769583367171308646013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2341026111156228411528017 1755769583367171308646013)
      ·
        refine ⟨658413593762689240742255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1755769583367171308646013 658413593762689240742255)
        ·
          refine ⟨987620390644033861113383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658413593762689240742255 987620390644033861113383)
          ·
            refine ⟨1481430585966050791670075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987620390644033861113383 1481430585966050791670075)
            ·
              refine ⟨2222145878949076187505113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481430585966050791670075 2222145878949076187505113)
              ·
                refine ⟨1666609409211807140628835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222145878949076187505113 1666609409211807140628835)
                ·
                  refine ⟨2499914113817710710943253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666609409211807140628835 2499914113817710710943253)
                  ·
                    refine ⟨117183474085205189575465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2499914113817710710943253 117183474085205189575465)
                    ·
                      rfl

theorem cell23_684642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_684642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684642 prefixEnd_684642 := by exact prefixLift 684642
  have htrace : WordTrace (prefixWord ++ tailWord_684642) baseStart_684642 baseEnd_684642 := by
    simpa [prefixWord, tailWord_684642, baseEnd_684642] using wordTrace_append hprefix tailTrace_684642
  have hstable : (prefixWord ++ tailWord_684642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684642).length < 2 ^ (prefixWord ++ tailWord_684642).sum := by decide
  have hdescent : baseEnd_684642 < baseStart_684642 := by decide
  rcases family_descends (prefixWord ++ tailWord_684642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684645 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_684645 : Nat := 118140960795 + 684645 * 2 ^ 59
def prefixEnd_684645 : Nat := 4983230072969 + 3 ^ 40 * 684645 * 2
def baseEnd_684645 : Nat := 351551962697579056988881

theorem tailTrace_684645 : CollatzResearch.WordTrace tailWord_684645 prefixEnd_684645 351551962697579056988881 := by
  unfold tailWord_684645
  simp only [CollatzResearch.WordTrace]
  refine ⟨24971054604655567901991389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16647369736437045267994259 24971054604655567901991389)
  ·
    refine ⟨9364145476745837963246771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24971054604655567901991389 9364145476745837963246771)
    ·
      refine ⟨14046218215118756944870157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9364145476745837963246771 14046218215118756944870157)
      ·
        refine ⟨5267331830669533854326309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14046218215118756944870157 5267331830669533854326309)
        ·
          refine ⟨987624718250537597686183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5267331830669533854326309 987624718250537597686183)
          ·
            refine ⟨1481437077375806396529275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987624718250537597686183 1481437077375806396529275)
            ·
              refine ⟨2222155616063709594793913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481437077375806396529275 2222155616063709594793913)
              ·
                refine ⟨1666616712047782196095435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222155616063709594793913 1666616712047782196095435)
                ·
                  refine ⟨2499925068071673294143153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666616712047782196095435 2499925068071673294143153)
                  ·
                    refine ⟨1874943801053754970607365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499925068071673294143153 1874943801053754970607365)
                    ·
                      refine ⟨351551962697579056988881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1874943801053754970607365 351551962697579056988881)
                      ·
                        rfl

theorem cell23_684645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_684645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684645 prefixEnd_684645 := by exact prefixLift 684645
  have htrace : WordTrace (prefixWord ++ tailWord_684645) baseStart_684645 baseEnd_684645 := by
    simpa [prefixWord, tailWord_684645, baseEnd_684645] using wordTrace_append hprefix tailTrace_684645
  have hstable : (prefixWord ++ tailWord_684645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684645).length < 2 ^ (prefixWord ++ tailWord_684645).sum := by decide
  have hdescent : baseEnd_684645 < baseStart_684645 := by decide
  rcases family_descends (prefixWord ++ tailWord_684645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684675 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 3, 3, 2]
def baseStart_684675 : Nat := 118140960795 + 684675 * 2 ^ 59
def prefixEnd_684675 : Nat := 4983230072969 + 3 ^ 40 * 684675 * 2
def baseEnd_684675 : Nat := 351567367117213939613743

theorem tailTrace_684675 : CollatzResearch.WordTrace tailWord_684675 prefixEnd_684675 351567367117213939613743 := by
  unfold tailWord_684675
  simp only [CollatzResearch.WordTrace]
  refine ⟨24972148794546883025583479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16648099196364588683722319 24972148794546883025583479)
  ·
    refine ⟨37458223191820324538375219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24972148794546883025583479 37458223191820324538375219)
    ·
      refine ⟨56187334787730486807562829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37458223191820324538375219 56187334787730486807562829)
      ·
        refine ⟨21070250545398932552836061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56187334787730486807562829 21070250545398932552836061)
        ·
          refine ⟨7901343954524599707313523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21070250545398932552836061 7901343954524599707313523)
          ·
            refine ⟨11852015931786899560970285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901343954524599707313523 11852015931786899560970285)
            ·
              refine ⟨4444505974420087335363857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11852015931786899560970285 4444505974420087335363857)
              ·
                refine ⟨3333379480815065501522893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4444505974420087335363857 3333379480815065501522893)
                ·
                  refine ⟨1250017305305649563071085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3333379480815065501522893 1250017305305649563071085)
                  ·
                    refine ⟨468756489489618586151657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250017305305649563071085 468756489489618586151657)
                    ·
                      refine ⟨351567367117213939613743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468756489489618586151657 351567367117213939613743)
                      ·
                        rfl

theorem cell23_684675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_684675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684675 prefixEnd_684675 := by exact prefixLift 684675
  have htrace : WordTrace (prefixWord ++ tailWord_684675) baseStart_684675 baseEnd_684675 := by
    simpa [prefixWord, tailWord_684675, baseEnd_684675] using wordTrace_append hprefix tailTrace_684675
  have hstable : (prefixWord ++ tailWord_684675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684675).length < 2 ^ (prefixWord ++ tailWord_684675).sum := by decide
  have hdescent : baseEnd_684675 < baseStart_684675 := by decide
  rcases family_descends (prefixWord ++ tailWord_684675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684682 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_684682 : Nat := 118140960795 + 684682 * 2 ^ 59
def prefixEnd_684682 : Nat := 4983230072969 + 3 ^ 40 * 684682 * 2
def baseEnd_684682 : Nat := 351570961481795412226211

theorem tailTrace_684682 : CollatzResearch.WordTrace tailWord_684682 prefixEnd_684682 351570961481795412226211 := by
  unfold tailWord_684682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243101026380380805272075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16648269403681015480725533 6243101026380380805272075)
  ·
    refine ⟨9364651539570571207908113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6243101026380380805272075 9364651539570571207908113)
    ·
      refine ⟨7023488654677928405931085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9364651539570571207908113 7023488654677928405931085)
      ·
        refine ⟨2633808245504223152224157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7023488654677928405931085 2633808245504223152224157)
        ·
          refine ⟨987678092064083682084059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633808245504223152224157 987678092064083682084059)
          ·
            refine ⟨1481517138096125523126089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987678092064083682084059 1481517138096125523126089)
            ·
              refine ⟨1111137853572094142344567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481517138096125523126089 1111137853572094142344567)
              ·
                refine ⟨1666706780358141213516851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111137853572094142344567 1666706780358141213516851)
                ·
                  refine ⟨2500060170537211820275277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666706780358141213516851 2500060170537211820275277)
                  ·
                    refine ⟨937522563951454432603229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500060170537211820275277 937522563951454432603229)
                    ·
                      refine ⟨351570961481795412226211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937522563951454432603229 351570961481795412226211)
                      ·
                        rfl

theorem cell23_684682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_684682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684682 prefixEnd_684682 := by exact prefixLift 684682
  have htrace : WordTrace (prefixWord ++ tailWord_684682) baseStart_684682 baseEnd_684682 := by
    simpa [prefixWord, tailWord_684682, baseEnd_684682] using wordTrace_append hprefix tailTrace_684682
  have hstable : (prefixWord ++ tailWord_684682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684682).length < 2 ^ (prefixWord ++ tailWord_684682).sum := by decide
  have hdescent : baseEnd_684682 < baseStart_684682 := by decide
  rcases family_descends (prefixWord ++ tailWord_684682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684708 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_684708 : Nat := 118140960795 + 684708 * 2 ^ 59
def prefixEnd_684708 : Nat := 4983230072969 + 3 ^ 40 * 684708 * 2
def baseEnd_684708 : Nat := 351584311978812310501091

theorem tailTrace_684708 : CollatzResearch.WordTrace tailWord_684708 prefixEnd_684708 351584311978812310501091 := by
  unfold tailWord_684708
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486676201713664830767389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16648901602284886441023185 12486676201713664830767389)
  ·
    refine ⟨4682503575642624311537771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12486676201713664830767389 4682503575642624311537771)
    ·
      refine ⟨7023755363463936467306657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4682503575642624311537771 7023755363463936467306657)
      ·
        refine ⟨5267816522597952350479993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7023755363463936467306657 5267816522597952350479993)
        ·
          refine ⟨3950862391948464262859995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5267816522597952350479993 3950862391948464262859995)
          ·
            refine ⟨5926293587922696394289993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950862391948464262859995 5926293587922696394289993)
            ·
              refine ⟨4444720190942022295717495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926293587922696394289993 4444720190942022295717495)
              ·
                refine ⟨6667080286413033443576243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444720190942022295717495 6667080286413033443576243)
                ·
                  refine ⟨10000620429619550165364365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667080286413033443576243 10000620429619550165364365)
                  ·
                    refine ⟨3750232661107331312011637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10000620429619550165364365 3750232661107331312011637)
                    ·
                      refine ⟨351584311978812310501091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3750232661107331312011637 351584311978812310501091)
                      ·
                        rfl

theorem cell23_684708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_684708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684708 prefixEnd_684708 := by exact prefixLift 684708
  have htrace : WordTrace (prefixWord ++ tailWord_684708) baseStart_684708 baseEnd_684708 := by
    simpa [prefixWord, tailWord_684708, baseEnd_684708] using wordTrace_append hprefix tailTrace_684708
  have hstable : (prefixWord ++ tailWord_684708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684708).length < 2 ^ (prefixWord ++ tailWord_684708).sum := by decide
  have hdescent : baseEnd_684708 < baseStart_684708 := by decide
  rcases family_descends (prefixWord ++ tailWord_684708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684768 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_684768 : Nat := 118140960795 + 684768 * 2 ^ 59
def prefixEnd_684768 : Nat := 4983230072969 + 3 ^ 40 * 684768 * 2
def baseEnd_684768 : Nat := 351615120818082075750815

theorem tailTrace_684768 : CollatzResearch.WordTrace tailWord_684768 prefixEnd_684768 351615120818082075750815 := by
  unfold tailWord_684768
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487770391604979954359479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16650360522139973272479305 12487770391604979954359479)
  ·
    refine ⟨18731655587407469931539219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12487770391604979954359479 18731655587407469931539219)
    ·
      refine ⟨28097483381111204897308829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18731655587407469931539219 28097483381111204897308829)
      ·
        refine ⟨10536556267916701836490811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28097483381111204897308829 10536556267916701836490811)
        ·
          refine ⟨15804834401875052754736217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10536556267916701836490811 15804834401875052754736217)
          ·
            refine ⟨11853625801406289566052163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15804834401875052754736217 11853625801406289566052163)
            ·
              refine ⟨17780438702109434349078245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11853625801406289566052163 17780438702109434349078245)
              ·
                refine ⟨3333832256645518940452171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17780438702109434349078245 3333832256645518940452171)
                ·
                  refine ⟨5000748384968278410678257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333832256645518940452171 5000748384968278410678257)
                  ·
                    refine ⟨3750561288726208808008693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000748384968278410678257 3750561288726208808008693)
                    ·
                      refine ⟨351615120818082075750815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3750561288726208808008693 351615120818082075750815)
                      ·
                        rfl

theorem cell23_684768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_684768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684768 prefixEnd_684768 := by exact prefixLift 684768
  have htrace : WordTrace (prefixWord ++ tailWord_684768) baseStart_684768 baseEnd_684768 := by
    simpa [prefixWord, tailWord_684768, baseEnd_684768] using wordTrace_append hprefix tailTrace_684768
  have hstable : (prefixWord ++ tailWord_684768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684768).length < 2 ^ (prefixWord ++ tailWord_684768).sum := by decide
  have hdescent : baseEnd_684768 < baseStart_684768 := by decide
  rcases family_descends (prefixWord ++ tailWord_684768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684795 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 6, 4, 2]
def baseStart_684795 : Nat := 118140960795 + 684795 * 2 ^ 59
def prefixEnd_684795 : Nat := 4983230072969 + 3 ^ 40 * 684795 * 2
def baseEnd_684795 : Nat := 351628984795753470113191

theorem tailTrace_684795 : CollatzResearch.WordTrace tailWord_684795 prefixEnd_684795 351628984795753470113191 := by
  unfold tailWord_684795
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976525554112143519951839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16651017036074762346634559 24976525554112143519951839)
  ·
    refine ⟨37464788331168215279927759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24976525554112143519951839 37464788331168215279927759)
    ·
      refine ⟨56197182496752322919891639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37464788331168215279927759 56197182496752322919891639)
      ·
        refine ⟨84295773745128484379837459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56197182496752322919891639 84295773745128484379837459)
        ·
          refine ⟨126443660617692726569756189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84295773745128484379837459 126443660617692726569756189)
          ·
            refine ⟨47416372731634772463658571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126443660617692726569756189 47416372731634772463658571)
            ·
              refine ⟨71124559097452158695487857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47416372731634772463658571 71124559097452158695487857)
              ·
                refine ⟨53343419323089119021615893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71124559097452158695487857 53343419323089119021615893)
                ·
                  refine ⟨2500472780769802454138245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53343419323089119021615893 2500472780769802454138245)
                  ·
                    refine ⟨468838646394337960150921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2500472780769802454138245 468838646394337960150921)
                    ·
                      refine ⟨351628984795753470113191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468838646394337960150921 351628984795753470113191)
                      ·
                        rfl

theorem cell23_684795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4, 2].length) (baseStart_684795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684795 prefixEnd_684795 := by exact prefixLift 684795
  have htrace : WordTrace (prefixWord ++ tailWord_684795) baseStart_684795 baseEnd_684795 := by
    simpa [prefixWord, tailWord_684795, baseEnd_684795] using wordTrace_append hprefix tailTrace_684795
  have hstable : (prefixWord ++ tailWord_684795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684795).length < 2 ^ (prefixWord ++ tailWord_684795).sum := by decide
  have hdescent : baseEnd_684795 < baseStart_684795 := by decide
  rcases family_descends (prefixWord ++ tailWord_684795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684805 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_684805 : Nat := 118140960795 + 684805 * 2 ^ 59
def prefixEnd_684805 : Nat := 4983230072969 + 3 ^ 40 * 684805 * 2
def baseEnd_684805 : Nat := 117211373200766143662715

theorem tailTrace_684805 : CollatzResearch.WordTrace tailWord_684805 prefixEnd_684805 117211373200766143662715 := by
  unfold tailWord_684805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976890284075915227815869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16651260189383943485210579 24976890284075915227815869)
  ·
    refine ⟨9366333856528468210430951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24976890284075915227815869 9366333856528468210430951)
    ·
      refine ⟨14049500784792702315646427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9366333856528468210430951 14049500784792702315646427)
      ·
        refine ⟨21074251177189053473469641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14049500784792702315646427 21074251177189053473469641)
        ·
          refine ⟨15805688382891790105102231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21074251177189053473469641 15805688382891790105102231)
          ·
            refine ⟨23708532574337685157653347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15805688382891790105102231 23708532574337685157653347)
            ·
              refine ⟨35562798861506527736480021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23708532574337685157653347 35562798861506527736480021)
              ·
                refine ⟨1667006196633118487647501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35562798861506527736480021 1667006196633118487647501)
                ·
                  refine ⟨625127323737419432867813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1667006196633118487647501 625127323737419432867813)
                  ·
                    refine ⟨117211373200766143662715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625127323737419432867813 117211373200766143662715)
                    ·
                      rfl

theorem cell23_684805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_684805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684805 prefixEnd_684805 := by exact prefixLift 684805
  have htrace : WordTrace (prefixWord ++ tailWord_684805) baseStart_684805 baseEnd_684805 := by
    simpa [prefixWord, tailWord_684805, baseEnd_684805] using wordTrace_append hprefix tailTrace_684805
  have hstable : (prefixWord ++ tailWord_684805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684805).length < 2 ^ (prefixWord ++ tailWord_684805).sum := by decide
  have hdescent : baseEnd_684805 < baseStart_684805 := by decide
  rcases family_descends (prefixWord ++ tailWord_684805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684832 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_684832 : Nat := 118140960795 + 684832 * 2 ^ 59
def prefixEnd_684832 : Nat := 4983230072969 + 3 ^ 40 * 684832 * 2
def baseEnd_684832 : Nat := 351647983579969825350521

theorem tailTrace_684832 : CollatzResearch.WordTrace tailWord_684832 prefixEnd_684832 351647983579969825350521 := by
  unfold tailWord_684832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488937527489049419524375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16651916703318732559365833 12488937527489049419524375)
  ·
    refine ⟨18733406291233574129286563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12488937527489049419524375 18733406291233574129286563)
    ·
      refine ⟨28100109436850361193929845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18733406291233574129286563 28100109436850361193929845)
      ·
        refine ⟨2634385259704721361930923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28100109436850361193929845 2634385259704721361930923)
        ·
          refine ⟨3951577889557082042896385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634385259704721361930923 3951577889557082042896385)
          ·
            refine ⟨2963683417167811532172289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3951577889557082042896385 2963683417167811532172289)
            ·
              refine ⟨2222762562875858649129217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963683417167811532172289 2222762562875858649129217)
              ·
                refine ⟨1667071922156893986846913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222762562875858649129217 1667071922156893986846913)
                ·
                  refine ⟨1250303941617670490135185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667071922156893986846913 1250303941617670490135185)
                  ·
                    refine ⟨937727956213252867601389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250303941617670490135185 937727956213252867601389)
                    ·
                      refine ⟨351647983579969825350521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937727956213252867601389 351647983579969825350521)
                      ·
                        rfl

theorem cell23_684832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_684832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684832 prefixEnd_684832 := by exact prefixLift 684832
  have htrace : WordTrace (prefixWord ++ tailWord_684832) baseStart_684832 baseEnd_684832 := by
    simpa [prefixWord, tailWord_684832, baseEnd_684832] using wordTrace_append hprefix tailTrace_684832
  have hstable : (prefixWord ++ tailWord_684832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684832).length < 2 ^ (prefixWord ++ tailWord_684832).sum := by decide
  have hdescent : baseEnd_684832 < baseStart_684832 := by decide
  rcases family_descends (prefixWord ++ tailWord_684832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684872 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_684872 : Nat := 118140960795 + 684872 * 2 ^ 59
def prefixEnd_684872 : Nat := 4983230072969 + 3 ^ 40 * 684872 * 2
def baseEnd_684872 : Nat := 351668522806149668850337

theorem tailTrace_684872 : CollatzResearch.WordTrace tailWord_684872 prefixEnd_684872 351668522806149668850337 := by
  unfold tailWord_684872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12489666987416592835252435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16652889316555457113669913 12489666987416592835252435)
  ·
    refine ⟨18734500481124889252878653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12489666987416592835252435 18734500481124889252878653)
    ·
      refine ⟨7025437680421833469829495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18734500481124889252878653 7025437680421833469829495)
      ·
        refine ⟨10538156520632750204744243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7025437680421833469829495 10538156520632750204744243)
        ·
          refine ⟨15807234780949125307116365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10538156520632750204744243 15807234780949125307116365)
          ·
            refine ⟨5927713042855921990168637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15807234780949125307116365 5927713042855921990168637)
            ·
              refine ⟨2222892391070970746313239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5927713042855921990168637 2222892391070970746313239)
              ·
                refine ⟨3334338586606456119469859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222892391070970746313239 3334338586606456119469859)
                ·
                  refine ⟨5001507879909684179204789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334338586606456119469859 5001507879909684179204789)
                  ·
                    refine ⟨468891363741532891800449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5001507879909684179204789 468891363741532891800449)
                    ·
                      refine ⟨351668522806149668850337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468891363741532891800449 351668522806149668850337)
                      ·
                        rfl

theorem cell23_684872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_684872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684872 prefixEnd_684872 := by exact prefixLift 684872
  have htrace : WordTrace (prefixWord ++ tailWord_684872) baseStart_684872 baseEnd_684872 := by
    simpa [prefixWord, tailWord_684872, baseEnd_684872] using wordTrace_append hprefix tailTrace_684872
  have hstable : (prefixWord ++ tailWord_684872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684872).length < 2 ^ (prefixWord ++ tailWord_684872).sum := by decide
  have hdescent : baseEnd_684872 < baseStart_684872 := by decide
  rcases family_descends (prefixWord ++ tailWord_684872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684882 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_684882 : Nat := 118140960795 + 684882 * 2 ^ 59
def prefixEnd_684882 : Nat := 4983230072969 + 3 ^ 40 * 684882 * 2
def baseEnd_684882 : Nat := 117224552537564876575097

theorem tailTrace_684882 : CollatzResearch.WordTrace tailWord_684882 prefixEnd_684882 117224552537564876575097 := by
  unfold tailWord_684882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6244924676199239344592225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16653132469864638252245933 6244924676199239344592225)
  ·
    refine ⟨4683693507149429508444169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6244924676199239344592225 4683693507149429508444169)
    ·
      refine ⟨3512770130362072131333127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4683693507149429508444169 3512770130362072131333127)
      ·
        refine ⟨5269155195543108196999691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512770130362072131333127 5269155195543108196999691)
        ·
          refine ⟨7903732793314662295499537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269155195543108196999691 7903732793314662295499537)
          ·
            refine ⟨5927799594985996721624653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7903732793314662295499537 5927799594985996721624653)
            ·
              refine ⟨2222924848119748770609245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5927799594985996721624653 2222924848119748770609245)
              ·
                refine ⟨833596818044905788978467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222924848119748770609245 833596818044905788978467)
                ·
                  refine ⟨1250395227067358683467701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833596818044905788978467 1250395227067358683467701)
                  ·
                    refine ⟨117224552537564876575097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1250395227067358683467701 117224552537564876575097)
                    ·
                      rfl

theorem cell23_684882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_684882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684882 prefixEnd_684882 := by exact prefixLift 684882
  have htrace : WordTrace (prefixWord ++ tailWord_684882) baseStart_684882 baseEnd_684882 := by
    simpa [prefixWord, tailWord_684882, baseEnd_684882] using wordTrace_append hprefix tailTrace_684882
  have hstable : (prefixWord ++ tailWord_684882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684882).length < 2 ^ (prefixWord ++ tailWord_684882).sum := by decide
  have hdescent : baseEnd_684882 < baseStart_684882 := by decide
  rcases family_descends (prefixWord ++ tailWord_684882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684912 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_684912 : Nat := 118140960795 + 684912 * 2 ^ 59
def prefixEnd_684912 : Nat := 4983230072969 + 3 ^ 40 * 684912 * 2
def baseEnd_684912 : Nat := 117229687344109837450051

theorem tailTrace_684912 : CollatzResearch.WordTrace tailWord_684912 prefixEnd_684912 117229687344109837450051 := by
  unfold tailWord_684912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490396447344136250980495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16653861929792181667973993 12490396447344136250980495)
  ·
    refine ⟨18735594671016204376470743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12490396447344136250980495 18735594671016204376470743)
    ·
      refine ⟨28103392006524306564706115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18735594671016204376470743 28103392006524306564706115)
      ·
        refine ⟨42155088009786459847059173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28103392006524306564706115 42155088009786459847059173)
        ·
          refine ⟨7904079001834961221323595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42155088009786459847059173 7904079001834961221323595)
          ·
            refine ⟨11856118502752441831985393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904079001834961221323595 11856118502752441831985393)
            ·
              refine ⟨8892088877064331373989045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11856118502752441831985393 8892088877064331373989045)
              ·
                refine ⟨833633332224781066311473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8892088877064331373989045 833633332224781066311473)
                ·
                  refine ⟨625224999168585799733605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833633332224781066311473 625224999168585799733605)
                  ·
                    refine ⟨117229687344109837450051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625224999168585799733605 117229687344109837450051)
                    ·
                      rfl

theorem cell23_684912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_684912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684912 prefixEnd_684912 := by exact prefixLift 684912
  have htrace : WordTrace (prefixWord ++ tailWord_684912) baseStart_684912 baseEnd_684912 := by
    simpa [prefixWord, tailWord_684912, baseEnd_684912] using wordTrace_append hprefix tailTrace_684912
  have hstable : (prefixWord ++ tailWord_684912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684912).length < 2 ^ (prefixWord ++ tailWord_684912).sum := by decide
  have hdescent : baseEnd_684912 < baseStart_684912 := by decide
  rcases family_descends (prefixWord ++ tailWord_684912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684969 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 3]
def baseStart_684969 : Nat := 118140960795 + 684969 * 2 ^ 59
def prefixEnd_684969 : Nat := 4983230072969 + 3 ^ 40 * 684969 * 2
def baseEnd_684969 : Nat := 351718330429635789337391

theorem tailTrace_684969 : CollatzResearch.WordTrace tailWord_684969 prefixEnd_684969 351718330429635789337391 := by
  unfold tailWord_684969
  simp only [CollatzResearch.WordTrace]
  refine ⟨24982871855481771236785961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16655247903654514157857307 24982871855481771236785961)
  ·
    refine ⟨18737153891611328427589471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24982871855481771236785961 18737153891611328427589471)
    ·
      refine ⟨28105730837416992641384207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18737153891611328427589471 28105730837416992641384207)
      ·
        refine ⟨42158596256125488962076311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28105730837416992641384207 42158596256125488962076311)
        ·
          refine ⟨63237894384188233443114467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42158596256125488962076311 63237894384188233443114467)
          ·
            refine ⟨94856841576282350164671701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63237894384188233443114467 94856841576282350164671701)
            ·
              refine ⟨2223207224444117581984493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94856841576282350164671701 2223207224444117581984493)
              ·
                refine ⟨833702709166544093244185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2223207224444117581984493 833702709166544093244185)
                ·
                  refine ⟨625277031874908069933139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833702709166544093244185 625277031874908069933139)
                  ·
                    refine ⟨937915547812362104899709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 625277031874908069933139 937915547812362104899709)
                    ·
                      refine ⟨351718330429635789337391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937915547812362104899709 351718330429635789337391)
                      ·
                        rfl

theorem cell23_684969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_684969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684969 prefixEnd_684969 := by exact prefixLift 684969
  have htrace : WordTrace (prefixWord ++ tailWord_684969) baseStart_684969 baseEnd_684969 := by
    simpa [prefixWord, tailWord_684969, baseEnd_684969] using wordTrace_append hprefix tailTrace_684969
  have hstable : (prefixWord ++ tailWord_684969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684969).length < 2 ^ (prefixWord ++ tailWord_684969).sum := by decide
  have hdescent : baseEnd_684969 < baseStart_684969 := by decide
  rcases family_descends (prefixWord ++ tailWord_684969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684975 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_684975 : Nat := 118140960795 + 684975 * 2 ^ 59
def prefixEnd_684975 : Nat := 4983230072969 + 3 ^ 40 * 684975 * 2
def baseEnd_684975 : Nat := 351721411313562765862363

theorem tailTrace_684975 : CollatzResearch.WordTrace tailWord_684975 prefixEnd_684975 351721411313562765862363 := by
  unfold tailWord_684975
  simp only [CollatzResearch.WordTrace]
  refine ⟨24983090693460034261504379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16655393795640022841002919 24983090693460034261504379)
  ·
    refine ⟨37474636040190051392256569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24983090693460034261504379 37474636040190051392256569)
    ·
      refine ⟨28105977030142538544192427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37474636040190051392256569 28105977030142538544192427)
      ·
        refine ⟨42158965545213807816288641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28105977030142538544192427 42158965545213807816288641)
        ·
          refine ⟨31619224158910355862216481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42158965545213807816288641 31619224158910355862216481)
          ·
            refine ⟨23714418119182766896662361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31619224158910355862216481 23714418119182766896662361)
            ·
              refine ⟨17785813589387075172496771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23714418119182766896662361 17785813589387075172496771)
              ·
                refine ⟨26678720384080612758745157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17785813589387075172496771 26678720384080612758745157)
                ·
                  refine ⟨5002260072015114892264717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26678720384080612758745157 5002260072015114892264717)
                  ·
                    refine ⟨1875847527005668084599269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5002260072015114892264717 1875847527005668084599269)
                    ·
                      refine ⟨351721411313562765862363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1875847527005668084599269 351721411313562765862363)
                      ·
                        rfl

theorem cell23_684975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_684975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684975 prefixEnd_684975 := by exact prefixLift 684975
  have htrace : WordTrace (prefixWord ++ tailWord_684975) baseStart_684975 baseEnd_684975 := by
    simpa [prefixWord, tailWord_684975, baseEnd_684975] using wordTrace_append hprefix tailTrace_684975
  have hstable : (prefixWord ++ tailWord_684975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684975).length < 2 ^ (prefixWord ++ tailWord_684975).sum := by decide
  have hdescent : baseEnd_684975 < baseStart_684975 := by decide
  rcases family_descends (prefixWord ++ tailWord_684975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684979 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 1, 3, 2]
def baseStart_684979 : Nat := 118140960795 + 684979 * 2 ^ 59
def prefixEnd_684979 : Nat := 4983230072969 + 3 ^ 40 * 684979 * 2
def baseEnd_684979 : Nat := 351723465236180750212345

theorem tailTrace_684979 : CollatzResearch.WordTrace tailWord_684979 prefixEnd_684979 351723465236180750212345 := by
  unfold tailWord_684979
  simp only [CollatzResearch.WordTrace]
  refine ⟨24983236585445542944649991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16655491056963695296433327 24983236585445542944649991)
  ·
    refine ⟨37474854878168314416974987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24983236585445542944649991 37474854878168314416974987)
    ·
      refine ⟨56212282317252471625462481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37474854878168314416974987 56212282317252471625462481)
      ·
        refine ⟨42159211737939353719096861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56212282317252471625462481 42159211737939353719096861)
        ·
          refine ⟨15809704401727257644661323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42159211737939353719096861 15809704401727257644661323)
          ·
            refine ⟨23714556602590886466991985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15809704401727257644661323 23714556602590886466991985)
            ·
              refine ⟨17785917451943164850243989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23714556602590886466991985 17785917451943164850243989)
              ·
                refine ⟨833714880559835852355187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17785917451943164850243989 833714880559835852355187)
                ·
                  refine ⟨1250572320839753778532781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833714880559835852355187 1250572320839753778532781)
                  ·
                    refine ⟨468964620314907666949793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250572320839753778532781 468964620314907666949793)
                    ·
                      refine ⟨351723465236180750212345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 468964620314907666949793 351723465236180750212345)
                      ·
                        rfl

theorem cell23_684979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3, 2].length) (baseStart_684979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684979 prefixEnd_684979 := by exact prefixLift 684979
  have htrace : WordTrace (prefixWord ++ tailWord_684979) baseStart_684979 baseEnd_684979 := by
    simpa [prefixWord, tailWord_684979, baseEnd_684979] using wordTrace_append hprefix tailTrace_684979
  have hstable : (prefixWord ++ tailWord_684979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684979).length < 2 ^ (prefixWord ++ tailWord_684979).sum := by decide
  have hdescent : baseEnd_684979 < baseStart_684979 := by decide
  rcases family_descends (prefixWord ++ tailWord_684979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684998 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_684998 : Nat := 118140960795 + 684998 * 2 ^ 59
def prefixEnd_684998 : Nat := 4983230072969 + 3 ^ 40 * 684998 * 2
def baseEnd_684998 : Nat := 351733221368616175874759

theorem tailTrace_684998 : CollatzResearch.WordTrace tailWord_684998 prefixEnd_684998 351733221368616175874759 := by
  unfold tailWord_684998
  simp only [CollatzResearch.WordTrace]
  refine ⟨780747799136772162174739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16655953048251139459727765 780747799136772162174739)
  ·
    refine ⟨1171121698705158243262109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 780747799136772162174739 1171121698705158243262109)
    ·
      refine ⟨439170637014434341223291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1171121698705158243262109 439170637014434341223291)
      ·
        refine ⟨658755955521651511834937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439170637014434341223291 658755955521651511834937)
        ·
          refine ⟨494066966641238633876203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658755955521651511834937 494066966641238633876203)
          ·
            refine ⟨741100449961857950814305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494066966641238633876203 741100449961857950814305)
            ·
              refine ⟨555825337471393463110729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741100449961857950814305 555825337471393463110729)
              ·
                refine ⟨416869003103545097333047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555825337471393463110729 416869003103545097333047)
                ·
                  refine ⟨625303504655317645999571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416869003103545097333047 625303504655317645999571)
                  ·
                    refine ⟨937955256982976468999357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 625303504655317645999571 937955256982976468999357)
                    ·
                      refine ⟨351733221368616175874759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 937955256982976468999357 351733221368616175874759)
                      ·
                        rfl

theorem cell23_684998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_684998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_684998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_684998 prefixEnd_684998 := by exact prefixLift 684998
  have htrace : WordTrace (prefixWord ++ tailWord_684998) baseStart_684998 baseEnd_684998 := by
    simpa [prefixWord, tailWord_684998, baseEnd_684998] using wordTrace_append hprefix tailTrace_684998
  have hstable : (prefixWord ++ tailWord_684998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684998).length < 2 ^ (prefixWord ++ tailWord_684998).sum := by decide
  have hdescent : baseEnd_684998 < baseStart_684998 := by decide
  rcases family_descends (prefixWord ++ tailWord_684998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685049 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 5]
def baseStart_685049 : Nat := 118140960795 + 685049 * 2 ^ 59
def prefixEnd_685049 : Nat := 4983230072969 + 3 ^ 40 * 685049 * 2
def baseEnd_685049 : Nat := 39084378764666164037447

theorem tailTrace_685049 : CollatzResearch.WordTrace tailWord_685049 prefixEnd_685049 39084378764666164037447 := by
  unfold tailWord_685049
  simp only [CollatzResearch.WordTrace]
  refine ⟨24985789695191944899698201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16657193130127963266465467 24985789695191944899698201)
  ·
    refine ⟨18739342271393958674773651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24985789695191944899698201 18739342271393958674773651)
    ·
      refine ⟨28109013407090938012160477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18739342271393958674773651 28109013407090938012160477)
      ·
        refine ⟨10540880027659101754560179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28109013407090938012160477 10540880027659101754560179)
        ·
          refine ⟨15811320041488652631840269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10540880027659101754560179 15811320041488652631840269)
          ·
            refine ⟨5929245015558244736940101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15811320041488652631840269 5929245015558244736940101)
            ·
              refine ⟨1111733440417170888176269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5929245015558244736940101 1111733440417170888176269)
              ·
                refine ⟨416900040156439083066101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1111733440417170888176269 416900040156439083066101)
                ·
                  refine ⟨39084378764666164037447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416900040156439083066101 39084378764666164037447)
                  ·
                    rfl

theorem cell23_685049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 5].length) (baseStart_685049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685049 prefixEnd_685049 := by exact prefixLift 685049
  have htrace : WordTrace (prefixWord ++ tailWord_685049) baseStart_685049 baseEnd_685049 := by
    simpa [prefixWord, tailWord_685049, baseEnd_685049] using wordTrace_append hprefix tailTrace_685049
  have hstable : (prefixWord ++ tailWord_685049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685049).length < 2 ^ (prefixWord ++ tailWord_685049).sum := by decide
  have hdescent : baseEnd_685049 < baseStart_685049 := by decide
  rcases family_descends (prefixWord ++ tailWord_685049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685082 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_685082 : Nat := 118140960795 + 685082 * 2 ^ 59
def prefixEnd_685082 : Nat := 4983230072969 + 3 ^ 40 * 685082 * 2
def baseEnd_685082 : Nat := 351776353743593847224371

theorem tailTrace_685082 : CollatzResearch.WordTrace tailWord_685082 prefixEnd_685082 351776353743593847224371 := by
  unfold tailWord_685082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246748326018097883912375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16657995536048261023766333 6246748326018097883912375)
  ·
    refine ⟨9370122489027146825868563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6246748326018097883912375 9370122489027146825868563)
    ·
      refine ⟨14055183733540720238802845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370122489027146825868563 14055183733540720238802845)
      ·
        refine ⟨5270693900077770089551067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14055183733540720238802845 5270693900077770089551067)
        ·
          refine ⟨7906040850116655134326601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270693900077770089551067 7906040850116655134326601)
          ·
            refine ⟨5929530637587491350744951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7906040850116655134326601 5929530637587491350744951)
            ·
              refine ⟨8894295956381237026117427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929530637587491350744951 8894295956381237026117427)
              ·
                refine ⟨13341443934571855539176141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8894295956381237026117427 13341443934571855539176141)
                ·
                  refine ⟨5003041475464445827191053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13341443934571855539176141 5003041475464445827191053)
                  ·
                    refine ⟨1876140553299167185196645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5003041475464445827191053 1876140553299167185196645)
                    ·
                      refine ⟨351776353743593847224371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1876140553299167185196645 351776353743593847224371)
                      ·
                        rfl

theorem cell23_685082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_685082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685082 prefixEnd_685082 := by exact prefixLift 685082
  have htrace : WordTrace (prefixWord ++ tailWord_685082) baseStart_685082 baseEnd_685082 := by
    simpa [prefixWord, tailWord_685082, baseEnd_685082] using wordTrace_append hprefix tailTrace_685082
  have hstable : (prefixWord ++ tailWord_685082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685082).length < 2 ^ (prefixWord ++ tailWord_685082).sum := by decide
  have hdescent : baseEnd_685082 < baseStart_685082 := by decide
  rcases family_descends (prefixWord ++ tailWord_685082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685150 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_685150 : Nat := 118140960795 + 685150 * 2 ^ 59
def prefixEnd_685150 : Nat := 4983230072969 + 3 ^ 40 * 685150 * 2
def baseEnd_685150 : Nat := 351811270428099581174059

theorem tailTrace_685150 : CollatzResearch.WordTrace tailWord_685150 prefixEnd_685150 351811270428099581174059 := by
  unfold tailWord_685150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123684183478254893640613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16659648978550692766083269 3123684183478254893640613)
  ·
    refine ⟨585690784402172792557615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3123684183478254893640613 585690784402172792557615)
    ·
      refine ⟨878536176603259188836423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585690784402172792557615 878536176603259188836423)
      ·
        refine ⟨1317804264904888783254635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878536176603259188836423 1317804264904888783254635)
        ·
          refine ⟨1976706397357333174881953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317804264904888783254635 1976706397357333174881953)
          ·
            refine ⟨1482529798017999881161465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976706397357333174881953 1482529798017999881161465)
            ·
              refine ⟨1111897348513499910871099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482529798017999881161465 1111897348513499910871099)
              ·
                refine ⟨1667846022770249866306649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111897348513499910871099 1667846022770249866306649)
                ·
                  refine ⟨1250884517077687399729987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667846022770249866306649 1250884517077687399729987)
                  ·
                    refine ⟨1876326775616531099594981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1250884517077687399729987 1876326775616531099594981)
                    ·
                      refine ⟨351811270428099581174059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1876326775616531099594981 351811270428099581174059)
                      ·
                        rfl

theorem cell23_685150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_685150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685150 prefixEnd_685150 := by exact prefixLift 685150
  have htrace : WordTrace (prefixWord ++ tailWord_685150) baseStart_685150 baseEnd_685150 := by
    simpa [prefixWord, tailWord_685150, baseEnd_685150] using wordTrace_append hprefix tailTrace_685150
  have hstable : (prefixWord ++ tailWord_685150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685150).length < 2 ^ (prefixWord ++ tailWord_685150).sum := by decide
  have hdescent : baseEnd_685150 < baseStart_685150 := by decide
  rcases family_descends (prefixWord ++ tailWord_685150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685173 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 6]
def baseStart_685173 : Nat := 118140960795 + 685173 * 2 ^ 59
def prefixEnd_685173 : Nat := 4983230072969 + 3 ^ 40 * 685173 * 2
def baseEnd_685173 : Nat := 39091453387016999020717

theorem tailTrace_685173 : CollatzResearch.WordTrace tailWord_685173 prefixEnd_685173 39091453387016999020717 := by
  unfold tailWord_685173
  simp only [CollatzResearch.WordTrace]
  refine ⟨24990312346742714077212173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16660208231161809384808115 24990312346742714077212173)
  ·
    refine ⟨9371367130028517778954565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24990312346742714077212173 9371367130028517778954565)
    ·
      refine ⟨1757131336880347083553981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9371367130028517778954565 1757131336880347083553981)
      ·
        refine ⟨658924251330130156332743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1757131336880347083553981 658924251330130156332743)
        ·
          refine ⟨988386376995195234499115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658924251330130156332743 988386376995195234499115)
          ·
            refine ⟨1482579565492792851748673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988386376995195234499115 1482579565492792851748673)
            ·
              refine ⟨1111934674119594638811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482579565492792851748673 1111934674119594638811505)
              ·
                refine ⟨833951005589695979108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111934674119594638811505 833951005589695979108629)
                ·
                  refine ⟨39091453387016999020717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 833951005589695979108629 39091453387016999020717)
                  ·
                    rfl

theorem cell23_685173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_685173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685173 prefixEnd_685173 := by exact prefixLift 685173
  have htrace : WordTrace (prefixWord ++ tailWord_685173) baseStart_685173 baseEnd_685173 := by
    simpa [prefixWord, tailWord_685173, baseEnd_685173] using wordTrace_append hprefix tailTrace_685173
  have hstable : (prefixWord ++ tailWord_685173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685173).length < 2 ^ (prefixWord ++ tailWord_685173).sum := by decide
  have hdescent : baseEnd_685173 < baseStart_685173 := by decide
  rcases family_descends (prefixWord ++ tailWord_685173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685176 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_685176 : Nat := 118140960795 + 685176 * 2 ^ 59
def prefixEnd_685176 : Nat := 4983230072969 + 3 ^ 40 * 685176 * 2
def baseEnd_685176 : Nat := 351824620925116479448939

theorem tailTrace_685176 : CollatzResearch.WordTrace tailWord_685176 prefixEnd_685176 351824620925116479448939 := by
  unfold tailWord_685176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12495210882865922794785691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16660281177154563726380921 12495210882865922794785691)
  ·
    refine ⟨18742816324298884192178537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12495210882865922794785691 18742816324298884192178537)
    ·
      refine ⟨14057112243224163144133903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18742816324298884192178537 14057112243224163144133903)
      ·
        refine ⟨21085668364836244716200855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14057112243224163144133903 21085668364836244716200855)
        ·
          refine ⟨31628502547254367074301283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21085668364836244716200855 31628502547254367074301283)
          ·
            refine ⟨47442753820881550611451925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31628502547254367074301283 47442753820881550611451925)
            ·
              refine ⟨2223879085353822684911809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47442753820881550611451925 2223879085353822684911809)
              ·
                refine ⟨1667909314015367013683857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223879085353822684911809 1667909314015367013683857)
                ·
                  refine ⟨1250931985511525260262893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667909314015367013683857 1250931985511525260262893)
                  ·
                    refine ⟨469099494566821972598585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250931985511525260262893 469099494566821972598585)
                    ·
                      refine ⟨351824620925116479448939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469099494566821972598585 351824620925116479448939)
                      ·
                        rfl

theorem cell23_685176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_685176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685176 prefixEnd_685176 := by exact prefixLift 685176
  have htrace : WordTrace (prefixWord ++ tailWord_685176) baseStart_685176 baseEnd_685176 := by
    simpa [prefixWord, tailWord_685176, baseEnd_685176] using wordTrace_append hprefix tailTrace_685176
  have hstable : (prefixWord ++ tailWord_685176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685176).length < 2 ^ (prefixWord ++ tailWord_685176).sum := by decide
  have hdescent : baseEnd_685176 < baseStart_685176 := by decide
  rcases family_descends (prefixWord ++ tailWord_685176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685177 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 1, 4]
def baseStart_685177 : Nat := 118140960795 + 685177 * 2 ^ 59
def prefixEnd_685177 : Nat := 4983230072969 + 3 ^ 40 * 685177 * 2
def baseEnd_685177 : Nat := 117275044801923658512145

theorem tailTrace_685177 : CollatzResearch.WordTrace tailWord_685177 prefixEnd_685177 117275044801923658512145 := by
  unfold tailWord_685177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24990458238728222760357785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16660305492485481840238523 24990458238728222760357785)
  ·
    refine ⟨18742843679046167070268339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24990458238728222760357785 18742843679046167070268339)
    ·
      refine ⟨28114265518569250605402509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18742843679046167070268339 28114265518569250605402509)
      ·
        refine ⟨10542849569463468977025941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28114265518569250605402509 10542849569463468977025941)
        ·
          refine ⟨494196073568600108298091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10542849569463468977025941 494196073568600108298091)
          ·
            refine ⟨741294110352900162447137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494196073568600108298091 741294110352900162447137)
            ·
              refine ⟨555970582764675121835353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741294110352900162447137 555970582764675121835353)
              ·
                refine ⟨416977937073506341376515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555970582764675121835353 416977937073506341376515)
                ·
                  refine ⟨625466905610259512064773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416977937073506341376515 625466905610259512064773)
                  ·
                    refine ⟨117275044801923658512145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625466905610259512064773 117275044801923658512145)
                    ·
                      rfl

theorem cell23_685177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 4].length) (baseStart_685177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685177 prefixEnd_685177 := by exact prefixLift 685177
  have htrace : WordTrace (prefixWord ++ tailWord_685177) baseStart_685177 baseEnd_685177 := by
    simpa [prefixWord, tailWord_685177, baseEnd_685177] using wordTrace_append hprefix tailTrace_685177
  have hstable : (prefixWord ++ tailWord_685177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685177).length < 2 ^ (prefixWord ++ tailWord_685177).sum := by decide
  have hdescent : baseEnd_685177 < baseStart_685177 := by decide
  rcases family_descends (prefixWord ++ tailWord_685177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685210 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_685210 : Nat := 118140960795 + 685210 * 2 ^ 59
def prefixEnd_685210 : Nat := 4983230072969 + 3 ^ 40 * 685210 * 2
def baseEnd_685210 : Nat := 351842079267369346423783

theorem tailTrace_685210 : CollatzResearch.WordTrace tailWord_685210 prefixEnd_685210 351842079267369346423783 := by
  unfold tailWord_685210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247915461902167349077271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16661107898405779597539389 6247915461902167349077271)
  ·
    refine ⟨9371873192853251023615907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6247915461902167349077271 9371873192853251023615907)
    ·
      refine ⟨14057809789279876535423861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9371873192853251023615907 14057809789279876535423861)
      ·
        refine ⟨1317919667744988425195987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14057809789279876535423861 1317919667744988425195987)
        ·
          refine ⟨1976879501617482637793981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317919667744988425195987 1976879501617482637793981)
          ·
            refine ⟨741329813106555989172743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1976879501617482637793981 741329813106555989172743)
            ·
              refine ⟨1111994719659833983759115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741329813106555989172743 1111994719659833983759115)
              ·
                refine ⟨1667992079489750975638673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111994719659833983759115 1667992079489750975638673)
                ·
                  refine ⟨1250994059617313231729005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667992079489750975638673 1250994059617313231729005)
                  ·
                    refine ⟨469122772356492461898377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250994059617313231729005 469122772356492461898377)
                    ·
                      refine ⟨351842079267369346423783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469122772356492461898377 351842079267369346423783)
                      ·
                        rfl

theorem cell23_685210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_685210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685210 prefixEnd_685210 := by exact prefixLift 685210
  have htrace : WordTrace (prefixWord ++ tailWord_685210) baseStart_685210 baseEnd_685210 := by
    simpa [prefixWord, tailWord_685210, baseEnd_685210] using wordTrace_append hprefix tailTrace_685210
  have hstable : (prefixWord ++ tailWord_685210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685210).length < 2 ^ (prefixWord ++ tailWord_685210).sum := by decide
  have hdescent : baseEnd_685210 < baseStart_685210 := by decide
  rcases family_descends (prefixWord ++ tailWord_685210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685223 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_685223 : Nat := 118140960795 + 685223 * 2 ^ 59
def prefixEnd_685223 : Nat := 4983230072969 + 3 ^ 40 * 685223 * 2
def baseEnd_685223 : Nat := 351848754515877795561223

theorem tailTrace_685223 : CollatzResearch.WordTrace tailWord_685223 prefixEnd_685223 351848754515877795561223 := by
  unfold tailWord_685223
  simp only [CollatzResearch.WordTrace]
  refine ⟨24992135996561572616532323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16661423997707715077688215 24992135996561572616532323)
  ·
    refine ⟨37488203994842358924798485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24992135996561572616532323 37488203994842358924798485)
    ·
      refine ⟨1757259562258235574599929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37488203994842358924798485 1757259562258235574599929)
      ·
        refine ⟨1317944671693676680949947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1757259562258235574599929 1317944671693676680949947)
        ·
          refine ⟨1976917007540515021424921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317944671693676680949947 1976917007540515021424921)
          ·
            refine ⟨1482687755655386266068691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976917007540515021424921 1482687755655386266068691)
            ·
              refine ⟨2224031633483079399103037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482687755655386266068691 2224031633483079399103037)
              ·
                refine ⟨834011862556154774663639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2224031633483079399103037 834011862556154774663639)
                ·
                  refine ⟨1251017793834232161995459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834011862556154774663639 1251017793834232161995459)
                  ·
                    refine ⟨1876526690751348242993189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1251017793834232161995459 1876526690751348242993189)
                    ·
                      refine ⟨351848754515877795561223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1876526690751348242993189 351848754515877795561223)
                      ·
                        rfl

theorem cell23_685223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_685223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685223 prefixEnd_685223 := by exact prefixLift 685223
  have htrace : WordTrace (prefixWord ++ tailWord_685223) baseStart_685223 baseEnd_685223 := by
    simpa [prefixWord, tailWord_685223, baseEnd_685223] using wordTrace_append hprefix tailTrace_685223
  have hstable : (prefixWord ++ tailWord_685223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685223).length < 2 ^ (prefixWord ++ tailWord_685223).sum := by decide
  have hdescent : baseEnd_685223 < baseStart_685223 := by decide
  rcases family_descends (prefixWord ++ tailWord_685223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685233 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_685233 : Nat := 118140960795 + 685233 * 2 ^ 59
def prefixEnd_685233 : Nat := 4983230072969 + 3 ^ 40 * 685233 * 2
def baseEnd_685233 : Nat := 117284629774140918812059

theorem tailTrace_685233 : CollatzResearch.WordTrace tailWord_685233 prefixEnd_685233 117284629774140918812059 := by
  unfold tailWord_685233
  simp only [CollatzResearch.WordTrace]
  refine ⟨24992500726525344324396353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16661667151016896216264235 24992500726525344324396353)
  ·
    refine ⟨18744375544894008243297265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24992500726525344324396353 18744375544894008243297265)
    ·
      refine ⟨14058281658670506182472949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18744375544894008243297265 14058281658670506182472949)
      ·
        refine ⟨1317963905500359954606839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14058281658670506182472949 1317963905500359954606839)
        ·
          refine ⟨1976945858250539931910259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317963905500359954606839 1976945858250539931910259)
          ·
            refine ⟨2965418787375809897865389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976945858250539931910259 2965418787375809897865389)
            ·
              refine ⟨1112032045265928711699521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2965418787375809897865389 1112032045265928711699521)
              ·
                refine ⟨834024033949446533774641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112032045265928711699521 834024033949446533774641)
                ·
                  refine ⟨625518025462084900330981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 834024033949446533774641 625518025462084900330981)
                  ·
                    refine ⟨117284629774140918812059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625518025462084900330981 117284629774140918812059)
                    ·
                      rfl

theorem cell23_685233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_685233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685233 prefixEnd_685233 := by exact prefixLift 685233
  have htrace : WordTrace (prefixWord ++ tailWord_685233) baseStart_685233 baseEnd_685233 := by
    simpa [prefixWord, tailWord_685233, baseEnd_685233] using wordTrace_append hprefix tailTrace_685233
  have hstable : (prefixWord ++ tailWord_685233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685233).length < 2 ^ (prefixWord ++ tailWord_685233).sum := by decide
  have hdescent : baseEnd_685233 < baseStart_685233 := by decide
  rcases family_descends (prefixWord ++ tailWord_685233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685256 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_685256 : Nat := 118140960795 + 685256 * 2 ^ 59
def prefixEnd_685256 : Nat := 4983230072969 + 3 ^ 40 * 685256 * 2
def baseEnd_685256 : Nat := 351865699377476166448571

theorem tailTrace_685256 : CollatzResearch.WordTrace tailWord_685256 prefixEnd_685256 351865699377476166448571 := by
  unfold tailWord_685256
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496669802721009626241811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16662226403628012834989081 12496669802721009626241811)
  ·
    refine ⟨18745004704081514439362717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12496669802721009626241811 18745004704081514439362717)
    ·
      refine ⟨7029376764030567914761019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18745004704081514439362717 7029376764030567914761019)
      ·
        refine ⟨10544065146045851872141529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029376764030567914761019 10544065146045851872141529)
        ·
          refine ⟨7908048859534388904106147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10544065146045851872141529 7908048859534388904106147)
          ·
            refine ⟨11862073289301583356159221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908048859534388904106147 11862073289301583356159221)
            ·
              refine ⟨1112069370872023439639927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11862073289301583356159221 1112069370872023439639927)
              ·
                refine ⟨1668104056308035159459891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112069370872023439639927 1668104056308035159459891)
                ·
                  refine ⟨2502156084462052739189837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668104056308035159459891 2502156084462052739189837)
                  ·
                    refine ⟨938308531673269777196189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2502156084462052739189837 938308531673269777196189)
                    ·
                      refine ⟨351865699377476166448571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 938308531673269777196189 351865699377476166448571)
                      ·
                        rfl

theorem cell23_685256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_685256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685256 prefixEnd_685256 := by exact prefixLift 685256
  have htrace : WordTrace (prefixWord ++ tailWord_685256) baseStart_685256 baseEnd_685256 := by
    simpa [prefixWord, tailWord_685256, baseEnd_685256] using wordTrace_append hprefix tailTrace_685256
  have hstable : (prefixWord ++ tailWord_685256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685256).length < 2 ^ (prefixWord ++ tailWord_685256).sum := by decide
  have hdescent : baseEnd_685256 < baseStart_685256 := by decide
  rcases family_descends (prefixWord ++ tailWord_685256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685316 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_685316 : Nat := 118140960795 + 685316 * 2 ^ 59
def prefixEnd_685316 : Nat := 4983230072969 + 3 ^ 40 * 685316 * 2
def baseEnd_685316 : Nat := 351896508216745931698295

theorem tailTrace_685316 : CollatzResearch.WordTrace tailWord_685316 prefixEnd_685316 351896508216745931698295 := by
  unfold tailWord_685316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12497763992612324749833901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16663685323483099666445201 12497763992612324749833901)
  ·
    refine ⟨4686661497229621781187713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12497763992612324749833901 4686661497229621781187713)
    ·
      refine ⟨3514996122922216335890785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4686661497229621781187713 3514996122922216335890785)
      ·
        refine ⟨2636247092191662251918089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3514996122922216335890785 2636247092191662251918089)
        ·
          refine ⟨1977185319143746688938567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2636247092191662251918089 1977185319143746688938567)
          ·
            refine ⟨2965777978715620033407851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977185319143746688938567 2965777978715620033407851)
            ·
              refine ⟨4448666968073430050111777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965777978715620033407851 4448666968073430050111777)
              ·
                refine ⟨3336500226055072537583833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4448666968073430050111777 3336500226055072537583833)
                ·
                  refine ⟨2502375169541304403187875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336500226055072537583833 2502375169541304403187875)
                  ·
                    refine ⟨3753562754311956604781813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2502375169541304403187875 3753562754311956604781813)
                    ·
                      refine ⟨351896508216745931698295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3753562754311956604781813 351896508216745931698295)
                      ·
                        rfl

theorem cell23_685316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_685316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685316 prefixEnd_685316 := by exact prefixLift 685316
  have htrace : WordTrace (prefixWord ++ tailWord_685316) baseStart_685316 baseEnd_685316 := by
    simpa [prefixWord, tailWord_685316, baseEnd_685316] using wordTrace_append hprefix tailTrace_685316
  have hstable : (prefixWord ++ tailWord_685316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685316).length < 2 ^ (prefixWord ++ tailWord_685316).sum := by decide
  have hdescent : baseEnd_685316 < baseStart_685316 := by decide
  rcases family_descends (prefixWord ++ tailWord_685316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685383 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 2, 5]
def baseStart_685383 : Nat := 118140960795 + 685383 * 2 ^ 59
def prefixEnd_685383 : Nat := 4983230072969 + 3 ^ 40 * 685383 * 2
def baseEnd_685383 : Nat := 117310303806865723186829

theorem tailTrace_685383 : CollatzResearch.WordTrace tailWord_685383 prefixEnd_685383 117310303806865723186829 := by
  unfold tailWord_685383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24997971675981919942356803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16665314450654613294904535 24997971675981919942356803)
  ·
    refine ⟨37496957513972879913535205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24997971675981919942356803 37496957513972879913535205)
    ·
      refine ⟨7030679533869914983787851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37496957513972879913535205 7030679533869914983787851)
      ·
        refine ⟨10546019300804872475681777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030679533869914983787851 10546019300804872475681777)
        ·
          refine ⟨7909514475603654356761333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10546019300804872475681777 7909514475603654356761333)
          ·
            refine ⟨741516982087842595946375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7909514475603654356761333 741516982087842595946375)
            ·
              refine ⟨1112275473131763893919563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741516982087842595946375 1112275473131763893919563)
              ·
                refine ⟨1668413209697645840879345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112275473131763893919563 1668413209697645840879345)
                ·
                  refine ⟨1251309907273234380659509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668413209697645840879345 1251309907273234380659509)
                  ·
                    refine ⟨117310303806865723186829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1251309907273234380659509 117310303806865723186829)
                    ·
                      rfl

theorem cell23_685383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_685383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685383 prefixEnd_685383 := by exact prefixLift 685383
  have htrace : WordTrace (prefixWord ++ tailWord_685383) baseStart_685383 baseEnd_685383 := by
    simpa [prefixWord, tailWord_685383, baseEnd_685383] using wordTrace_append hprefix tailTrace_685383
  have hstable : (prefixWord ++ tailWord_685383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685383).length < 2 ^ (prefixWord ++ tailWord_685383).sum := by decide
  have hdescent : baseEnd_685383 < baseStart_685383 := by decide
  rcases family_descends (prefixWord ++ tailWord_685383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685413 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_685413 : Nat := 118140960795 + 685413 * 2 ^ 59
def prefixEnd_685413 : Nat := 4983230072969 + 3 ^ 40 * 685413 * 2
def baseEnd_685413 : Nat := 117315438613410684061783

theorem tailTrace_685413 : CollatzResearch.WordTrace tailWord_685413 prefixEnd_685413 117315438613410684061783 := by
  unfold tailWord_685413
  simp only [CollatzResearch.WordTrace]
  refine ⟨24999065865873235065948893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16666043910582156710632595 24999065865873235065948893)
  ·
    refine ⟨9374649699702463149730835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24999065865873235065948893 9374649699702463149730835)
    ·
      refine ⟨14061974549553694724596253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9374649699702463149730835 14061974549553694724596253)
      ·
        refine ⟨5273240456082635521723595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14061974549553694724596253 5273240456082635521723595)
        ·
          refine ⟨7909860684123953282585393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273240456082635521723595 7909860684123953282585393)
          ·
            refine ⟨5932395513092964961939045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7909860684123953282585393 5932395513092964961939045)
            ·
              refine ⟨1112324158704930930363571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5932395513092964961939045 1112324158704930930363571)
              ·
                refine ⟨1668486238057396395545357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112324158704930930363571 1668486238057396395545357)
                ·
                  refine ⟨625682339271523648329509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1668486238057396395545357 625682339271523648329509)
                  ·
                    refine ⟨117315438613410684061783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625682339271523648329509 117315438613410684061783)
                    ·
                      rfl

theorem cell23_685413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_685413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685413 prefixEnd_685413 := by exact prefixLift 685413
  have htrace : WordTrace (prefixWord ++ tailWord_685413) baseStart_685413 baseEnd_685413 := by
    simpa [prefixWord, tailWord_685413, baseEnd_685413] using wordTrace_append hprefix tailTrace_685413
  have hstable : (prefixWord ++ tailWord_685413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685413).length < 2 ^ (prefixWord ++ tailWord_685413).sum := by decide
  have hdescent : baseEnd_685413 < baseStart_685413 := by decide
  rcases family_descends (prefixWord ++ tailWord_685413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685436 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_685436 : Nat := 118140960795 + 685436 * 2 ^ 59
def prefixEnd_685436 : Nat := 4983230072969 + 3 ^ 40 * 685436 * 2
def baseEnd_685436 : Nat := 351958125895285462197743

theorem tailTrace_685436 : CollatzResearch.WordTrace tailWord_685436 prefixEnd_685436 351958125895285462197743 := by
  unfold tailWord_685436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499952372394954997018081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16666603163193273329357441 12499952372394954997018081)
  ·
    refine ⟨9374964279296216247763561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12499952372394954997018081 9374964279296216247763561)
    ·
      refine ⟨7031223209472162185822671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9374964279296216247763561 7031223209472162185822671)
      ·
        refine ⟨10546834814208243278734007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031223209472162185822671 10546834814208243278734007)
        ·
          refine ⟨15820252221312364918101011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546834814208243278734007 15820252221312364918101011)
          ·
            refine ⟨23730378331968547377151517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15820252221312364918101011 23730378331968547377151517)
            ·
              refine ⟨8898891874488205266431819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23730378331968547377151517 8898891874488205266431819)
              ·
                refine ⟨13348337811732307899647729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8898891874488205266431819 13348337811732307899647729)
                ·
                  refine ⟨10011253358799230924735797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13348337811732307899647729 10011253358799230924735797)
                  ·
                    refine ⟨938555002387427899193981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10011253358799230924735797 938555002387427899193981)
                    ·
                      refine ⟨351958125895285462197743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 938555002387427899193981 351958125895285462197743)
                      ·
                        rfl

theorem cell23_685436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_685436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685436 prefixEnd_685436 := by exact prefixLift 685436
  have htrace : WordTrace (prefixWord ++ tailWord_685436) baseStart_685436 baseEnd_685436 := by
    simpa [prefixWord, tailWord_685436, baseEnd_685436] using wordTrace_append hprefix tailTrace_685436
  have hstable : (prefixWord ++ tailWord_685436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685436).length < 2 ^ (prefixWord ++ tailWord_685436).sum := by decide
  have hdescent : baseEnd_685436 < baseStart_685436 := by decide
  rcases family_descends (prefixWord ++ tailWord_685436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685447 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 1, 4]
def baseStart_685447 : Nat := 118140960795 + 685447 * 2 ^ 59
def prefixEnd_685447 : Nat := 4983230072969 + 3 ^ 40 * 685447 * 2
def baseEnd_685447 : Nat := 117321258060828306386731

theorem tailTrace_685447 : CollatzResearch.WordTrace tailWord_685447 prefixEnd_685447 117321258060828306386731 := by
  unfold tailWord_685447
  simp only [CollatzResearch.WordTrace]
  refine ⟨25000305947750058872686595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16666870631833372581791063 25000305947750058872686595)
  ·
    refine ⟨37500458921625088309029893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25000305947750058872686595 37500458921625088309029893)
    ·
      refine ⟨7031336047804704057943105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37500458921625088309029893 7031336047804704057943105)
      ·
        refine ⟨5273502035853528043457329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7031336047804704057943105 5273502035853528043457329)
        ·
          refine ⟨3955126526890146032592997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5273502035853528043457329 3955126526890146032592997)
          ·
            refine ⟨741586223791902381111187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3955126526890146032592997 741586223791902381111187)
            ·
              refine ⟨1112379335687853571666781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741586223791902381111187 1112379335687853571666781)
              ·
                refine ⟨417142250882945089375043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1112379335687853571666781 417142250882945089375043)
                ·
                  refine ⟨625713376324417634062565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417142250882945089375043 625713376324417634062565)
                  ·
                    refine ⟨117321258060828306386731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625713376324417634062565 117321258060828306386731)
                    ·
                      rfl

theorem cell23_685447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_685447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685447 prefixEnd_685447 := by exact prefixLift 685447
  have htrace : WordTrace (prefixWord ++ tailWord_685447) baseStart_685447 baseEnd_685447 := by
    simpa [prefixWord, tailWord_685447, baseEnd_685447] using wordTrace_append hprefix tailTrace_685447
  have hstable : (prefixWord ++ tailWord_685447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685447).length < 2 ^ (prefixWord ++ tailWord_685447).sum := by decide
  have hdescent : baseEnd_685447 < baseStart_685447 := by decide
  rcases family_descends (prefixWord ++ tailWord_685447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685464 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 1, 4]
def baseStart_685464 : Nat := 118140960795 + 685464 * 2 ^ 59
def prefixEnd_685464 : Nat := 4983230072969 + 3 ^ 40 * 685464 * 2
def baseEnd_685464 : Nat := 117324167784537117549205

theorem tailTrace_685464 : CollatzResearch.WordTrace tailWord_685464 prefixEnd_685464 117324167784537117549205 := by
  unfold tailWord_685464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500462994344235388027723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16667283992458980517370297 12500462994344235388027723)
  ·
    refine ⟨18750694491516353082041585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12500462994344235388027723 18750694491516353082041585)
    ·
      refine ⟨14063020868637264811531189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18750694491516353082041585 14063020868637264811531189)
      ·
        refine ⟨1318408206434743576081049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14063020868637264811531189 1318408206434743576081049)
        ·
          refine ⟨988806154826057682060787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1318408206434743576081049 988806154826057682060787)
          ·
            refine ⟨1483209232239086523091181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988806154826057682060787 1483209232239086523091181)
            ·
              refine ⟨556203462089657446159193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1483209232239086523091181 556203462089657446159193)
              ·
                refine ⟨417152596567243084619395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556203462089657446159193 417152596567243084619395)
                ·
                  refine ⟨625728894850864626929093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417152596567243084619395 625728894850864626929093)
                  ·
                    refine ⟨117324167784537117549205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625728894850864626929093 117324167784537117549205)
                    ·
                      rfl

theorem cell23_685464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_685464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685464 prefixEnd_685464 := by exact prefixLift 685464
  have htrace : WordTrace (prefixWord ++ tailWord_685464) baseStart_685464 baseEnd_685464 := by
    simpa [prefixWord, tailWord_685464, baseEnd_685464] using wordTrace_append hprefix tailTrace_685464
  have hstable : (prefixWord ++ tailWord_685464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685464).length < 2 ^ (prefixWord ++ tailWord_685464).sum := by decide
  have hdescent : baseEnd_685464 < baseStart_685464 := by decide
  rcases family_descends (prefixWord ++ tailWord_685464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685476 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_685476 : Nat := 118140960795 + 685476 * 2 ^ 59
def prefixEnd_685476 : Nat := 4983230072969 + 3 ^ 40 * 685476 * 2
def baseEnd_685476 : Nat := 351978665121465305697559

theorem tailTrace_685476 : CollatzResearch.WordTrace tailWord_685476 prefixEnd_685476 351978665121465305697559 := by
  unfold tailWord_685476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500681832322498412746141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16667575776429997883661521 12500681832322498412746141)
  ·
    refine ⟨4687755687120936904779803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12500681832322498412746141 4687755687120936904779803)
    ·
      refine ⟨7031633530681405357169705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687755687120936904779803 7031633530681405357169705)
      ·
        refine ⟨5273725148011054017877279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7031633530681405357169705 5273725148011054017877279)
        ·
          refine ⟨7910587722016581026815919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273725148011054017877279 7910587722016581026815919)
          ·
            refine ⟨11865881583024871540223879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910587722016581026815919 11865881583024871540223879)
            ·
              refine ⟨17798822374537307310335819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865881583024871540223879 17798822374537307310335819)
              ·
                refine ⟨26698233561805960965503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17798822374537307310335819 26698233561805960965503729)
                ·
                  refine ⟨20023675171354470724127797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26698233561805960965503729 20023675171354470724127797)
                  ·
                    refine ⟨1877219547314481630386981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20023675171354470724127797 1877219547314481630386981)
                    ·
                      refine ⟨351978665121465305697559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1877219547314481630386981 351978665121465305697559)
                      ·
                        rfl

theorem cell23_685476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_685476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685476 prefixEnd_685476 := by exact prefixLift 685476
  have htrace : WordTrace (prefixWord ++ tailWord_685476) baseStart_685476 baseEnd_685476 := by
    simpa [prefixWord, tailWord_685476, baseEnd_685476] using wordTrace_append hprefix tailTrace_685476
  have hstable : (prefixWord ++ tailWord_685476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685476).length < 2 ^ (prefixWord ++ tailWord_685476).sum := by decide
  have hdescent : baseEnd_685476 < baseStart_685476 := by decide
  rcases family_descends (prefixWord ++ tailWord_685476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685496 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_685496 : Nat := 118140960795 + 685496 * 2 ^ 59
def prefixEnd_685496 : Nat := 4983230072969 + 3 ^ 40 * 685496 * 2
def baseEnd_685496 : Nat := 351988934734555227447467

theorem tailTrace_685496 : CollatzResearch.WordTrace tailWord_685496 prefixEnd_685496 351988934734555227447467 := by
  unfold tailWord_685496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501046562286270120610171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16668062083048360160813561 12501046562286270120610171)
  ·
    refine ⟨18751569843429405180915257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12501046562286270120610171 18751569843429405180915257)
    ·
      refine ⟨14063677382572053885686443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18751569843429405180915257 14063677382572053885686443)
      ·
        refine ⟨21095516073858080828529665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063677382572053885686443 21095516073858080828529665)
        ·
          refine ⟨15821637055393560621397249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21095516073858080828529665 15821637055393560621397249)
          ·
            refine ⟨11866227791545170466047937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15821637055393560621397249 11866227791545170466047937)
            ·
              refine ⟨8899670843658877849535953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11866227791545170466047937 8899670843658877849535953)
              ·
                refine ⟨6674753132744158387151965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8899670843658877849535953 6674753132744158387151965)
                ·
                  refine ⟨2503032424779059395181987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6674753132744158387151965 2503032424779059395181987)
                  ·
                    refine ⟨3754548637168589092772981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503032424779059395181987 3754548637168589092772981)
                    ·
                      refine ⟨351988934734555227447467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3754548637168589092772981 351988934734555227447467)
                      ·
                        rfl

theorem cell23_685496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_685496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685496 prefixEnd_685496 := by exact prefixLift 685496
  have htrace : WordTrace (prefixWord ++ tailWord_685496) baseStart_685496 baseEnd_685496 := by
    simpa [prefixWord, tailWord_685496, baseEnd_685496] using wordTrace_append hprefix tailTrace_685496
  have hstable : (prefixWord ++ tailWord_685496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685496).length < 2 ^ (prefixWord ++ tailWord_685496).sum := by decide
  have hdescent : baseEnd_685496 < baseStart_685496 := by decide
  rcases family_descends (prefixWord ++ tailWord_685496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685497 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 2, 3, 2]
def baseStart_685497 : Nat := 118140960795 + 685497 * 2 ^ 59
def prefixEnd_685497 : Nat := 4983230072969 + 3 ^ 40 * 685497 * 2
def baseEnd_685497 : Nat := 351989448215209723534963

theorem tailTrace_685497 : CollatzResearch.WordTrace tailWord_685497 prefixEnd_685497 351989448215209723534963 := by
  unfold tailWord_685497
  simp only [CollatzResearch.WordTrace]
  refine ⟨25002129597568917412006745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16668086398379278274671163 25002129597568917412006745)
  ·
    refine ⟨18751597198176688059005059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25002129597568917412006745 18751597198176688059005059)
    ·
      refine ⟨28127395797265032088507589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18751597198176688059005059 28127395797265032088507589)
      ·
        refine ⟨5273886711987193516595173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28127395797265032088507589 5273886711987193516595173)
        ·
          refine ⟨988853758497598784361595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5273886711987193516595173 988853758497598784361595)
          ·
            refine ⟨1483280637746398176542393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988853758497598784361595 1483280637746398176542393)
            ·
              refine ⟨1112460478309798632406795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483280637746398176542393 1112460478309798632406795)
              ·
                refine ⟨1668690717464697948610193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112460478309798632406795 1668690717464697948610193)
                ·
                  refine ⟨1251518038098523461457645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668690717464697948610193 1251518038098523461457645)
                  ·
                    refine ⟨469319264286946298046617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251518038098523461457645 469319264286946298046617)
                    ·
                      refine ⟨351989448215209723534963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469319264286946298046617 351989448215209723534963)
                      ·
                        rfl

theorem cell23_685497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_685497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685497 prefixEnd_685497 := by exact prefixLift 685497
  have htrace : WordTrace (prefixWord ++ tailWord_685497) baseStart_685497 baseEnd_685497 := by
    simpa [prefixWord, tailWord_685497, baseEnd_685497] using wordTrace_append hprefix tailTrace_685497
  have hstable : (prefixWord ++ tailWord_685497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685497).length < 2 ^ (prefixWord ++ tailWord_685497).sum := by decide
  have hdescent : baseEnd_685497 < baseStart_685497 := by decide
  rcases family_descends (prefixWord ++ tailWord_685497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685516 : List Nat := [2, 2, 1, 4, 2, 12]
def baseStart_685516 : Nat := 118140960795 + 685516 * 2 ^ 59
def prefixEnd_685516 : Nat := 4983230072969 + 3 ^ 40 * 685516 * 2
def baseEnd_685516 : Nat := 1448556396492366869125

theorem tailTrace_685516 : CollatzResearch.WordTrace tailWord_685516 prefixEnd_685516 1448556396492366869125 := by
  unfold tailWord_685516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501411292250041828474201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16668548389666722437965601 12501411292250041828474201)
  ·
    refine ⟨9376058469187531371355651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12501411292250041828474201 9376058469187531371355651)
    ·
      refine ⟨14064087703781297057033477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9376058469187531371355651 14064087703781297057033477)
      ·
        refine ⟨2637016444458993198193777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14064087703781297057033477 2637016444458993198193777)
        ·
          refine ⟨1977762333344244898645333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637016444458993198193777 1977762333344244898645333)
          ·
            refine ⟨1448556396492366869125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1977762333344244898645333 1448556396492366869125)
            ·
              rfl

theorem cell23_685516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 12].length) (baseStart_685516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685516 prefixEnd_685516 := by exact prefixLift 685516
  have htrace : WordTrace (prefixWord ++ tailWord_685516) baseStart_685516 baseEnd_685516 := by
    simpa [prefixWord, tailWord_685516, baseEnd_685516] using wordTrace_append hprefix tailTrace_685516
  have hstable : (prefixWord ++ tailWord_685516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685516).length < 2 ^ (prefixWord ++ tailWord_685516).sum := by decide
  have hdescent : baseEnd_685516 < baseStart_685516 := by decide
  rcases family_descends (prefixWord ++ tailWord_685516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685533 : List Nat := [1, 4, 3, 1, 1, 2, 3, 8]
def baseStart_685533 : Nat := 118140960795 + 685533 * 2 ^ 59
def prefixEnd_685533 : Nat := 4983230072969 + 3 ^ 40 * 685533 * 2
def baseEnd_685533 : Nat := 13037330871065614173511

theorem tailTrace_685533 : CollatzResearch.WordTrace tailWord_685533 prefixEnd_685533 13037330871065614173511 := by
  unfold tailWord_685533
  simp only [CollatzResearch.WordTrace]
  refine ⟨25003442625438495560317253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16668961750292330373544835 25003442625438495560317253)
  ·
    refine ⟨4688145492269717917559485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25003442625438495560317253 4688145492269717917559485)
    ·
      refine ⟨1758054559601144219084807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4688145492269717917559485 1758054559601144219084807)
      ·
        refine ⟨2637081839401716328627211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758054559601144219084807 2637081839401716328627211)
        ·
          refine ⟨3955622759102574492940817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637081839401716328627211 3955622759102574492940817)
          ·
            refine ⟨2966717069326930869705613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955622759102574492940817 2966717069326930869705613)
            ·
              refine ⟨1112518900997599076139605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966717069326930869705613 1112518900997599076139605)
              ·
                refine ⟨13037330871065614173511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1112518900997599076139605 13037330871065614173511)
                ·
                  rfl

theorem cell23_685533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 8].length) (baseStart_685533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685533 prefixEnd_685533 := by exact prefixLift 685533
  have htrace : WordTrace (prefixWord ++ tailWord_685533) baseStart_685533 baseEnd_685533 := by
    simpa [prefixWord, tailWord_685533, baseEnd_685533] using wordTrace_append hprefix tailTrace_685533
  have hstable : (prefixWord ++ tailWord_685533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685533).length < 2 ^ (prefixWord ++ tailWord_685533).sum := by decide
  have hdescent : baseEnd_685533 < baseStart_685533 := by decide
  rcases family_descends (prefixWord ++ tailWord_685533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685598 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_685598 : Nat := 118140960795 + 685598 * 2 ^ 59
def prefixEnd_685598 : Nat := 4983230072969 + 3 ^ 40 * 685598 * 2
def baseEnd_685598 : Nat := 352041309761313828371999

theorem tailTrace_685598 : CollatzResearch.WordTrace tailWord_685598 prefixEnd_685598 352041309761313828371999 := by
  unfold tailWord_685598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125726671275376457679181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16670542246802007774288965 3125726671275376457679181)
  ·
    refine ⟨1172147501728266171629693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3125726671275376457679181 1172147501728266171629693)
    ·
      refine ⟨439555313148099814361135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1172147501728266171629693 439555313148099814361135)
      ·
        refine ⟨659332969722149721541703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439555313148099814361135 659332969722149721541703)
        ·
          refine ⟨988999454583224582312555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659332969722149721541703 988999454583224582312555)
          ·
            refine ⟨1483499181874836873468833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988999454583224582312555 1483499181874836873468833)
            ·
              refine ⟨1112624386406127655101625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483499181874836873468833 1112624386406127655101625)
              ·
                refine ⟨834468289804595741326219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112624386406127655101625 834468289804595741326219)
                ·
                  refine ⟨1251702434706893611989329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834468289804595741326219 1251702434706893611989329)
                  ·
                    refine ⟨938776826030170208991997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1251702434706893611989329 938776826030170208991997)
                    ·
                      refine ⟨352041309761313828371999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 938776826030170208991997 352041309761313828371999)
                      ·
                        rfl

theorem cell23_685598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_685598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685598 prefixEnd_685598 := by exact prefixLift 685598
  have htrace : WordTrace (prefixWord ++ tailWord_685598) baseStart_685598 baseEnd_685598 := by
    simpa [prefixWord, tailWord_685598, baseEnd_685598] using wordTrace_append hprefix tailTrace_685598
  have hstable : (prefixWord ++ tailWord_685598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685598).length < 2 ^ (prefixWord ++ tailWord_685598).sum := by decide
  have hdescent : baseEnd_685598 < baseStart_685598 := by decide
  rcases family_descends (prefixWord ++ tailWord_685598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685633 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_685633 : Nat := 118140960795 + 685633 * 2 ^ 59
def prefixEnd_685633 : Nat := 4983230072969 + 3 ^ 40 * 685633 * 2
def baseEnd_685633 : Nat := 352059281584221191434337

theorem tailTrace_685633 : CollatzResearch.WordTrace tailWord_685633 prefixEnd_685633 352059281584221191434337 := by
  unfold tailWord_685633
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007089925076212638957553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671393283384141759305035 25007089925076212638957553)
  ·
    refine ⟨18755317443807159479218165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25007089925076212638957553 18755317443807159479218165)
    ·
      refine ⟨1758311010356921201176703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18755317443807159479218165 1758311010356921201176703)
      ·
        refine ⟨2637466515535381801765055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758311010356921201176703 2637466515535381801765055)
        ·
          refine ⟨3956199773303072702647583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637466515535381801765055 3956199773303072702647583)
          ·
            refine ⟨5934299659954609053971375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956199773303072702647583 5934299659954609053971375)
            ·
              refine ⟨8901449489931913580957063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934299659954609053971375 8901449489931913580957063)
              ·
                refine ⟨13352174234897870371435595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8901449489931913580957063 13352174234897870371435595)
                ·
                  refine ⟨20028261352346805557153393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13352174234897870371435595 20028261352346805557153393)
                  ·
                    refine ⟨15021196014260104167865045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20028261352346805557153393 15021196014260104167865045)
                    ·
                      refine ⟨352059281584221191434337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15021196014260104167865045 352059281584221191434337)
                      ·
                        rfl

theorem cell23_685633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_685633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685633 prefixEnd_685633 := by exact prefixLift 685633
  have htrace : WordTrace (prefixWord ++ tailWord_685633) baseStart_685633 baseEnd_685633 := by
    simpa [prefixWord, tailWord_685633, baseEnd_685633] using wordTrace_append hprefix tailTrace_685633
  have hstable : (prefixWord ++ tailWord_685633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685633).length < 2 ^ (prefixWord ++ tailWord_685633).sum := by decide
  have hdescent : baseEnd_685633 < baseStart_685633 := by decide
  rcases family_descends (prefixWord ++ tailWord_685633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685653 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_685653 : Nat := 118140960795 + 685653 * 2 ^ 59
def prefixEnd_685653 : Nat := 4983230072969 + 3 ^ 40 * 685653 * 2
def baseEnd_685653 : Nat := 117356517065770371061415

theorem tailTrace_685653 : CollatzResearch.WordTrace tailWord_685653 prefixEnd_685653 117356517065770371061415 := by
  unfold tailWord_685653
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007819385003756054685613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671879590002504036457075 25007819385003756054685613)
  ·
    refine ⟨9377932269376408520507105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25007819385003756054685613 9377932269376408520507105)
    ·
      refine ⟨7033449202032306390380329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9377932269376408520507105 7033449202032306390380329)
      ·
        refine ⟨5275086901524229792785247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7033449202032306390380329 5275086901524229792785247)
        ·
          refine ⟨7912630352286344689177871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5275086901524229792785247 7912630352286344689177871)
          ·
            refine ⟨11868945528429517033766807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7912630352286344689177871 11868945528429517033766807)
            ·
              refine ⟨17803418292644275550650211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11868945528429517033766807 17803418292644275550650211)
              ·
                refine ⟨26705127438966413325975317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17803418292644275550650211 26705127438966413325975317)
                ·
                  refine ⟨1251802848701550624655093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26705127438966413325975317 1251802848701550624655093)
                  ·
                    refine ⟨117356517065770371061415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1251802848701550624655093 117356517065770371061415)
                    ·
                      rfl

theorem cell23_685653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_685653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685653 prefixEnd_685653 := by exact prefixLift 685653
  have htrace : WordTrace (prefixWord ++ tailWord_685653) baseStart_685653 baseEnd_685653 := by
    simpa [prefixWord, tailWord_685653, baseEnd_685653] using wordTrace_append hprefix tailTrace_685653
  have hstable : (prefixWord ++ tailWord_685653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685653).length < 2 ^ (prefixWord ++ tailWord_685653).sum := by decide
  have hdescent : baseEnd_685653 < baseStart_685653 := by decide
  rcases family_descends (prefixWord ++ tailWord_685653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685673 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_685673 : Nat := 118140960795 + 685673 * 2 ^ 59
def prefixEnd_685673 : Nat := 4983230072969 + 3 ^ 40 * 685673 * 2
def baseEnd_685673 : Nat := 352079820810401034934153

theorem tailTrace_685673 : CollatzResearch.WordTrace tailWord_685673 prefixEnd_685673 352079820810401034934153 := by
  unfold tailWord_685673
  simp only [CollatzResearch.WordTrace]
  refine ⟨25008548844931299470413673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16672365896620866313609115 25008548844931299470413673)
  ·
    refine ⟨18756411633698474602810255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25008548844931299470413673 18756411633698474602810255)
    ·
      refine ⟨28134617450547711904215383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18756411633698474602810255 28134617450547711904215383)
      ·
        refine ⟨42201926175821567856323075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28134617450547711904215383 42201926175821567856323075)
        ·
          refine ⟨63302889263732351784484613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42201926175821567856323075 63302889263732351784484613)
          ·
            refine ⟨11869291736949815959590865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63302889263732351784484613 11869291736949815959590865)
            ·
              refine ⟨8901968802712361969693149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11869291736949815959590865 8901968802712361969693149)
              ·
                refine ⟨3338238301017135738634931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8901968802712361969693149 3338238301017135738634931)
                ·
                  refine ⟨5007357451525703607952397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338238301017135738634931 5007357451525703607952397)
                  ·
                    refine ⟨1877759044322138852982149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5007357451525703607952397 1877759044322138852982149)
                    ·
                      refine ⟨352079820810401034934153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1877759044322138852982149 352079820810401034934153)
                      ·
                        rfl

theorem cell23_685673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_685673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685673 prefixEnd_685673 := by exact prefixLift 685673
  have htrace : WordTrace (prefixWord ++ tailWord_685673) baseStart_685673 baseEnd_685673 := by
    simpa [prefixWord, tailWord_685673, baseEnd_685673] using wordTrace_append hprefix tailTrace_685673
  have hstable : (prefixWord ++ tailWord_685673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685673).length < 2 ^ (prefixWord ++ tailWord_685673).sum := by decide
  have hdescent : baseEnd_685673 < baseStart_685673 := by decide
  rcases family_descends (prefixWord ++ tailWord_685673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685724 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_685724 : Nat := 118140960795 + 685724 * 2 ^ 59
def prefixEnd_685724 : Nat := 4983230072969 + 3 ^ 40 * 685724 * 2
def baseEnd_685724 : Nat := 352106008323780335396419

theorem tailTrace_685724 : CollatzResearch.WordTrace tailWord_685724 prefixEnd_685724 352106008323780335396419 := by
  unfold tailWord_685724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505204483873267590260113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16673605978497690120346817 12505204483873267590260113)
  ·
    refine ⟨9378903362904950692695085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12505204483873267590260113 9378903362904950692695085)
    ·
      refine ⟨3517088761089356509760657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9378903362904950692695085 3517088761089356509760657)
      ·
        refine ⟨2637816570817017382320493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3517088761089356509760657 2637816570817017382320493)
        ·
          refine ⟨989181214056381518370185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2637816570817017382320493 989181214056381518370185)
          ·
            refine ⟨741885910542286138777639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989181214056381518370185 741885910542286138777639)
            ·
              refine ⟨1112828865813429208166459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741885910542286138777639 1112828865813429208166459)
              ·
                refine ⟨1669243298720143812249689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112828865813429208166459 1669243298720143812249689)
                ·
                  refine ⟨1251932474040107859187267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669243298720143812249689 1251932474040107859187267)
                  ·
                    refine ⟨1877898711060161788780901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1251932474040107859187267 1877898711060161788780901)
                    ·
                      refine ⟨352106008323780335396419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1877898711060161788780901 352106008323780335396419)
                      ·
                        rfl

theorem cell23_685724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_685724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685724 prefixEnd_685724 := by exact prefixLift 685724
  have htrace : WordTrace (prefixWord ++ tailWord_685724) baseStart_685724 baseEnd_685724 := by
    simpa [prefixWord, tailWord_685724, baseEnd_685724] using wordTrace_append hprefix tailTrace_685724
  have hstable : (prefixWord ++ tailWord_685724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685724).length < 2 ^ (prefixWord ++ tailWord_685724).sum := by decide
  have hdescent : baseEnd_685724 < baseStart_685724 := by decide
  rcases family_descends (prefixWord ++ tailWord_685724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685777 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_685777 : Nat := 118140960795 + 685777 * 2 ^ 59
def prefixEnd_685777 : Nat := 4983230072969 + 3 ^ 40 * 685777 * 2
def baseEnd_685777 : Nat := 117377740932822876011225

theorem tailTrace_685777 : CollatzResearch.WordTrace tailWord_685777 prefixEnd_685777 117377740932822876011225 := by
  unfold tailWord_685777
  simp only [CollatzResearch.WordTrace]
  refine ⟨25012342036554525232199585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16674894691036350154799723 25012342036554525232199585)
  ·
    refine ⟨18759256527415893924149689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25012342036554525232199585 18759256527415893924149689)
    ·
      refine ⟨14069442395561920443112267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18759256527415893924149689 14069442395561920443112267)
      ·
        refine ⟨21104163593342880664668401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14069442395561920443112267 21104163593342880664668401)
        ·
          refine ⟨15828122695007160498501301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21104163593342880664668401 15828122695007160498501301)
          ·
            refine ⟨1483886502656921296734497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15828122695007160498501301 1483886502656921296734497)
            ·
              refine ⟨1112914876992690972550873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483886502656921296734497 1112914876992690972550873)
              ·
                refine ⟨834686157744518229413155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112914876992690972550873 834686157744518229413155)
                ·
                  refine ⟨1252029236616777344119733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834686157744518229413155 1252029236616777344119733)
                  ·
                    refine ⟨117377740932822876011225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1252029236616777344119733 117377740932822876011225)
                    ·
                      rfl

theorem cell23_685777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_685777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685777 prefixEnd_685777 := by exact prefixLift 685777
  have htrace : WordTrace (prefixWord ++ tailWord_685777) baseStart_685777 baseEnd_685777 := by
    simpa [prefixWord, tailWord_685777, baseEnd_685777] using wordTrace_append hprefix tailTrace_685777
  have hstable : (prefixWord ++ tailWord_685777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685777).length < 2 ^ (prefixWord ++ tailWord_685777).sum := by decide
  have hdescent : baseEnd_685777 < baseStart_685777 := by decide
  rcases family_descends (prefixWord ++ tailWord_685777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685797 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_685797 : Nat := 118140960795 + 685797 * 2 ^ 59
def prefixEnd_685797 : Nat := 4983230072969 + 3 ^ 40 * 685797 * 2
def baseEnd_685797 : Nat := 352143492411558549783583

theorem tailTrace_685797 : CollatzResearch.WordTrace tailWord_685797 prefixEnd_685797 352143492411558549783583 := by
  unfold tailWord_685797
  simp only [CollatzResearch.WordTrace]
  refine ⟨25013071496482068647927645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16675380997654712431951763 25013071496482068647927645)
  ·
    refine ⟨9379901811180775742972867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25013071496482068647927645 9379901811180775742972867)
    ·
      refine ⟨14069852716771163614459301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379901811180775742972867 14069852716771163614459301)
      ·
        refine ⟨2638097384394593177711119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14069852716771163614459301 2638097384394593177711119)
        ·
          refine ⟨3957146076591889766566679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638097384394593177711119 3957146076591889766566679)
          ·
            refine ⟨5935719114887834649850019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957146076591889766566679 5935719114887834649850019)
            ·
              refine ⟨8903578672331751974775029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935719114887834649850019 8903578672331751974775029)
              ·
                refine ⟨834710500531101747635159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8903578672331751974775029 834710500531101747635159)
                ·
                  refine ⟨1252065750796652621452739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834710500531101747635159 1252065750796652621452739)
                  ·
                    refine ⟨1878098626194978932179109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252065750796652621452739 1878098626194978932179109)
                    ·
                      refine ⟨352143492411558549783583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1878098626194978932179109 352143492411558549783583)
                      ·
                        rfl

theorem cell23_685797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_685797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685797 prefixEnd_685797 := by exact prefixLift 685797
  have htrace : WordTrace (prefixWord ++ tailWord_685797) baseStart_685797 baseEnd_685797 := by
    simpa [prefixWord, tailWord_685797, baseEnd_685797] using wordTrace_append hprefix tailTrace_685797
  have hstable : (prefixWord ++ tailWord_685797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685797).length < 2 ^ (prefixWord ++ tailWord_685797).sum := by decide
  have hdescent : baseEnd_685797 < baseStart_685797 := by decide
  rcases family_descends (prefixWord ++ tailWord_685797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685803 : List Nat := [1, 1, 1, 1, 2, 4, 13]
def baseStart_685803 : Nat := 118140960795 + 685803 * 2 ^ 59
def prefixEnd_685803 : Nat := 4983230072969 + 3 ^ 40 * 685803 * 2
def baseEnd_685803 : Nat := 4347488559203525016155

theorem tailTrace_685803 : CollatzResearch.WordTrace tailWord_685803 prefixEnd_685803 4347488559203525016155 := by
  unfold tailWord_685803
  simp only [CollatzResearch.WordTrace]
  refine ⟨25013290334460331672646063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16675526889640221115097375 25013290334460331672646063)
  ·
    refine ⟨37519935501690497508969095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25013290334460331672646063 37519935501690497508969095)
    ·
      refine ⟨56279903252535746263453643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37519935501690497508969095 56279903252535746263453643)
      ·
        refine ⟨84419854878803619395180465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56279903252535746263453643 84419854878803619395180465)
        ·
          refine ⟨63314891159102714546385349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84419854878803619395180465 63314891159102714546385349)
          ·
            refine ⟨11871542092331758977447253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63314891159102714546385349 11871542092331758977447253)
            ·
              refine ⟨4347488559203525016155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 11871542092331758977447253 4347488559203525016155)
              ·
                rfl

theorem cell23_685803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 13].length) (baseStart_685803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685803 prefixEnd_685803 := by exact prefixLift 685803
  have htrace : WordTrace (prefixWord ++ tailWord_685803) baseStart_685803 baseEnd_685803 := by
    simpa [prefixWord, tailWord_685803, baseEnd_685803] using wordTrace_append hprefix tailTrace_685803
  have hstable : (prefixWord ++ tailWord_685803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685803).length < 2 ^ (prefixWord ++ tailWord_685803).sum := by decide
  have hdescent : baseEnd_685803 < baseStart_685803 := by decide
  rcases family_descends (prefixWord ++ tailWord_685803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685807 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 2, 4]
def baseStart_685807 : Nat := 118140960795 + 685807 * 2 ^ 59
def prefixEnd_685807 : Nat := 4983230072969 + 3 ^ 40 * 685807 * 2
def baseEnd_685807 : Nat := 117382875739367836886179

theorem tailTrace_685807 : CollatzResearch.WordTrace tailWord_685807 prefixEnd_685807 117382875739367836886179 := by
  unfold tailWord_685807
  simp only [CollatzResearch.WordTrace]
  refine ⟨25013436226445840355791675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16675624150963893570527783 25013436226445840355791675)
  ·
    refine ⟨37520154339668760533687513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25013436226445840355791675 37520154339668760533687513)
    ·
      refine ⟨28140115754751570400265635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37520154339668760533687513 28140115754751570400265635)
      ·
        refine ⟨42210173632127355600398453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28140115754751570400265635 42210173632127355600398453)
        ·
          refine ⟨3957203778011939587537355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42210173632127355600398453 3957203778011939587537355)
          ·
            refine ⟨5935805667017909381306033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957203778011939587537355 5935805667017909381306033)
            ·
              refine ⟨4451854250263432035979525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935805667017909381306033 4451854250263432035979525)
              ·
                refine ⟨834722671924393506746161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4451854250263432035979525 834722671924393506746161)
                ·
                  refine ⟨626042003943295130059621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 834722671924393506746161 626042003943295130059621)
                  ·
                    refine ⟨117382875739367836886179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626042003943295130059621 117382875739367836886179)
                    ·
                      rfl

theorem cell23_685807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_685807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685807 prefixEnd_685807 := by exact prefixLift 685807
  have htrace : WordTrace (prefixWord ++ tailWord_685807) baseStart_685807 baseEnd_685807 := by
    simpa [prefixWord, tailWord_685807, baseEnd_685807] using wordTrace_append hprefix tailTrace_685807
  have hstable : (prefixWord ++ tailWord_685807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685807).length < 2 ^ (prefixWord ++ tailWord_685807).sum := by decide
  have hdescent : baseEnd_685807 < baseStart_685807 := by decide
  rcases family_descends (prefixWord ++ tailWord_685807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685810 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_685810 : Nat := 118140960795 + 685810 * 2 ^ 59
def prefixEnd_685810 : Nat := 4983230072969 + 3 ^ 40 * 685810 * 2
def baseEnd_685810 : Nat := 352150167660066998921023

theorem tailTrace_685810 : CollatzResearch.WordTrace tailWord_685810 prefixEnd_685810 352150167660066998921023 := by
  unfold tailWord_685810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253386411358742967037721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16675697096956647912100589 6253386411358742967037721)
  ·
    refine ⟨4690039808519057225278291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6253386411358742967037721 4690039808519057225278291)
    ·
      refine ⟨7035059712778585837917437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690039808519057225278291 7035059712778585837917437)
      ·
        refine ⟨2638147392291969689219039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7035059712778585837917437 2638147392291969689219039)
        ·
          refine ⟨3957221088437954533828559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638147392291969689219039 3957221088437954533828559)
          ·
            refine ⟨5935831632656931800742839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957221088437954533828559 5935831632656931800742839)
            ·
              refine ⟨8903747448985397701114259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935831632656931800742839 8903747448985397701114259)
              ·
                refine ⟨13355621173478096551671389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8903747448985397701114259 13355621173478096551671389)
                ·
                  refine ⟨5008357940054286206876771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13355621173478096551671389 5008357940054286206876771)
                  ·
                    refine ⟨7512536910081429310315157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008357940054286206876771 7512536910081429310315157)
                    ·
                      refine ⟨352150167660066998921023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7512536910081429310315157 352150167660066998921023)
                      ·
                        rfl

theorem cell23_685810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_685810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685810 prefixEnd_685810 := by exact prefixLift 685810
  have htrace : WordTrace (prefixWord ++ tailWord_685810) baseStart_685810 baseEnd_685810 := by
    simpa [prefixWord, tailWord_685810, baseEnd_685810] using wordTrace_append hprefix tailTrace_685810
  have hstable : (prefixWord ++ tailWord_685810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685810).length < 2 ^ (prefixWord ++ tailWord_685810).sum := by decide
  have hdescent : baseEnd_685810 < baseStart_685810 := by decide
  rcases family_descends (prefixWord ++ tailWord_685810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685820 : List Nat := [2, 2, 2, 1, 3, 1, 4, 8]
def baseStart_685820 : Nat := 118140960795 + 685820 * 2 ^ 59
def prefixEnd_685820 : Nat := 4983230072969 + 3 ^ 40 * 685820 * 2
def baseEnd_685820 : Nat := 13042788980244887399851

theorem tailTrace_685820 : CollatzResearch.WordTrace tailWord_685820 prefixEnd_685820 13042788980244887399851 := by
  unfold tailWord_685820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506955187699371788007457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16675940250265829050676609 12506955187699371788007457)
  ·
    refine ⟨9380216390774528841005593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12506955187699371788007457 9380216390774528841005593)
    ·
      refine ⟨7035162293080896630754195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9380216390774528841005593 7035162293080896630754195)
      ·
        refine ⟨10552743439621344946131293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035162293080896630754195 10552743439621344946131293)
        ·
          refine ⟨3957278789858004354799235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10552743439621344946131293 3957278789858004354799235)
          ·
            refine ⟨5935918184787006532198853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957278789858004354799235 5935918184787006532198853)
            ·
              refine ⟨1112984659647563724787285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5935918184787006532198853 1112984659647563724787285)
              ·
                refine ⟨13042788980244887399851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1112984659647563724787285 13042788980244887399851)
                ·
                  rfl

theorem cell23_685820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 8].length) (baseStart_685820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685820 prefixEnd_685820 := by exact prefixLift 685820
  have htrace : WordTrace (prefixWord ++ tailWord_685820) baseStart_685820 baseEnd_685820 := by
    simpa [prefixWord, tailWord_685820, baseEnd_685820] using wordTrace_append hprefix tailTrace_685820
  have hstable : (prefixWord ++ tailWord_685820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685820).length < 2 ^ (prefixWord ++ tailWord_685820).sum := by decide
  have hdescent : baseEnd_685820 < baseStart_685820 := by decide
  rcases family_descends (prefixWord ++ tailWord_685820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685831 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_685831 : Nat := 118140960795 + 685831 * 2 ^ 59
def prefixEnd_685831 : Nat := 4983230072969 + 3 ^ 40 * 685831 * 2
def baseEnd_685831 : Nat := 352160950753811416758427

theorem tailTrace_685831 : CollatzResearch.WordTrace tailWord_685831 prefixEnd_685831 352160950753811416758427 := by
  unfold tailWord_685831
  simp only [CollatzResearch.WordTrace]
  refine ⟨25014311578358892454665347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16676207718905928303110231 25014311578358892454665347)
  ·
    refine ⟨37521467367538338681998021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25014311578358892454665347 37521467367538338681998021)
    ·
      refine ⟨7035275131413438502874629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37521467367538338681998021 7035275131413438502874629)
      ·
        refine ⟨1319114087140019719288993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7035275131413438502874629 1319114087140019719288993)
        ·
          refine ⟨989335565355014789466745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319114087140019719288993 989335565355014789466745)
          ·
            refine ⟨742001674016261092100059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989335565355014789466745 742001674016261092100059)
            ·
              refine ⟨1113002511024391638150089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742001674016261092100059 1113002511024391638150089)
              ·
                refine ⟨834751883268293728612567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113002511024391638150089 834751883268293728612567)
                ·
                  refine ⟨1252127824902440592918851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834751883268293728612567 1252127824902440592918851)
                  ·
                    refine ⟨1878191737353660889378277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252127824902440592918851 1878191737353660889378277)
                    ·
                      refine ⟨352160950753811416758427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1878191737353660889378277 352160950753811416758427)
                      ·
                        rfl

theorem cell23_685831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_685831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685831 prefixEnd_685831 := by exact prefixLift 685831
  have htrace : WordTrace (prefixWord ++ tailWord_685831) baseStart_685831 baseEnd_685831 := by
    simpa [prefixWord, tailWord_685831, baseEnd_685831] using wordTrace_append hprefix tailTrace_685831
  have hstable : (prefixWord ++ tailWord_685831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685831).length < 2 ^ (prefixWord ++ tailWord_685831).sum := by decide
  have hdescent : baseEnd_685831 < baseStart_685831 := by decide
  rcases family_descends (prefixWord ++ tailWord_685831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685834 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_685834 : Nat := 118140960795 + 685834 * 2 ^ 59
def prefixEnd_685834 : Nat := 4983230072969 + 3 ^ 40 * 685834 * 2
def baseEnd_685834 : Nat := 352162491195774905020913

theorem tailTrace_685834 : CollatzResearch.WordTrace tailWord_685834 prefixEnd_685834 352162491195774905020913 := by
  unfold tailWord_685834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253605249337005991756139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16676280664898682644683037 6253605249337005991756139)
  ·
    refine ⟨9380407874005508987634209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6253605249337005991756139 9380407874005508987634209)
    ·
      refine ⟨7035305905504131740725657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9380407874005508987634209 7035305905504131740725657)
      ·
        refine ⟨5276479429128098805544243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7035305905504131740725657 5276479429128098805544243)
        ·
          refine ⟨7914719143692148208316365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276479429128098805544243 7914719143692148208316365)
          ·
            refine ⟨2968019678884555578118637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7914719143692148208316365 2968019678884555578118637)
            ·
              refine ⟨1113007379581708341794489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2968019678884555578118637 1113007379581708341794489)
              ·
                refine ⟨834755534686281256345867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113007379581708341794489 834755534686281256345867)
                ·
                  refine ⟨1252133302029421884518801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834755534686281256345867 1252133302029421884518801)
                  ·
                    refine ⟨939099976522066413389101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1252133302029421884518801 939099976522066413389101)
                    ·
                      refine ⟨352162491195774905020913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939099976522066413389101 352162491195774905020913)
                      ·
                        rfl

theorem cell23_685834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_685834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685834 prefixEnd_685834 := by exact prefixLift 685834
  have htrace : WordTrace (prefixWord ++ tailWord_685834) baseStart_685834 baseEnd_685834 := by
    simpa [prefixWord, tailWord_685834, baseEnd_685834] using wordTrace_append hprefix tailTrace_685834
  have hstable : (prefixWord ++ tailWord_685834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685834).length < 2 ^ (prefixWord ++ tailWord_685834).sum := by decide
  have hdescent : baseEnd_685834 < baseStart_685834 := by decide
  rcases family_descends (prefixWord ++ tailWord_685834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685847 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_685847 : Nat := 118140960795 + 685847 * 2 ^ 59
def prefixEnd_685847 : Nat := 4983230072969 + 3 ^ 40 * 685847 * 2
def baseEnd_685847 : Nat := 352169166444283354158353

theorem tailTrace_685847 : CollatzResearch.WordTrace tailWord_685847 prefixEnd_685847 352169166444283354158353 := by
  unfold tailWord_685847
  simp only [CollatzResearch.WordTrace]
  refine ⟨25014895146300927187247795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16676596764200618124831863 25014895146300927187247795)
  ·
    refine ⟨37522342719451390780871693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25014895146300927187247795 37522342719451390780871693)
    ·
      refine ⟨14070878519794271542826885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37522342719451390780871693 14070878519794271542826885)
      ·
        refine ⟨2638289722461425914280041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14070878519794271542826885 2638289722461425914280041)
        ·
          refine ⟨1978717291846069435710031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638289722461425914280041 1978717291846069435710031)
          ·
            refine ⟨2968075937769104153565047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978717291846069435710031 2968075937769104153565047)
            ·
              refine ⟨4452113906653656230347571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968075937769104153565047 4452113906653656230347571)
              ·
                refine ⟨6678170859980484345521357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452113906653656230347571 6678170859980484345521357)
                ·
                  refine ⟨2504314072492681629570509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6678170859980484345521357 2504314072492681629570509)
                  ·
                    refine ⟨939117777184755611088941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504314072492681629570509 939117777184755611088941)
                    ·
                      refine ⟨352169166444283354158353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939117777184755611088941 352169166444283354158353)
                      ·
                        rfl

theorem cell23_685847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_685847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685847 prefixEnd_685847 := by exact prefixLift 685847
  have htrace : WordTrace (prefixWord ++ tailWord_685847) baseStart_685847 baseEnd_685847 := by
    simpa [prefixWord, tailWord_685847, baseEnd_685847] using wordTrace_append hprefix tailTrace_685847
  have hstable : (prefixWord ++ tailWord_685847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685847).length < 2 ^ (prefixWord ++ tailWord_685847).sum := by decide
  have hdescent : baseEnd_685847 < baseStart_685847 := by decide
  rcases family_descends (prefixWord ++ tailWord_685847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
