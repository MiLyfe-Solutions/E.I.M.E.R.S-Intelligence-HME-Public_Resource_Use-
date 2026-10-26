import V185TrunkScan23Chunk1412

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8370764 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_8370764 : Nat := 118140960795 + 8370764 * 2 ^ 59
def prefixEnd_8370764 : Nat := 4983230072969 + 3 ^ 40 * 8370764 * 2
def baseEnd_8370764 : Nat := 4298225377352392581053563

theorem tailTrace_8370764 : CollatzResearch.WordTrace tailWord_8370764 prefixEnd_8370764 4298225377352392581053563 := by
  unfold tailWord_8370764
  simp only [CollatzResearch.WordTrace]
  refine ⟨152653422523079557759515673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203537896697439410346020897 152653422523079557759515673)
  ·
    refine ⟨114490066892309668319636755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152653422523079557759515673 114490066892309668319636755)
    ·
      refine ⟨171735100338464502479455133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114490066892309668319636755 171735100338464502479455133)
      ·
        refine ⟨64400662626924188429795675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171735100338464502479455133 64400662626924188429795675)
        ·
          refine ⟨96600993940386282644693513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64400662626924188429795675 96600993940386282644693513)
          ·
            refine ⟨72450745455289711983520135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96600993940386282644693513 72450745455289711983520135)
            ·
              refine ⟨108676118182934567975280203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72450745455289711983520135 108676118182934567975280203)
              ·
                refine ⟨163014177274401851962920305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108676118182934567975280203 163014177274401851962920305)
                ·
                  refine ⟨122260632955801388972190229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163014177274401851962920305 122260632955801388972190229)
                  ·
                    refine ⟨5730967169803190108071417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122260632955801388972190229 5730967169803190108071417)
                    ·
                      refine ⟨4298225377352392581053563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5730967169803190108071417 4298225377352392581053563)
                      ·
                        rfl

theorem cell23_8370764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_8370764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370764 prefixEnd_8370764 := by exact prefixLift 8370764
  have htrace : WordTrace (prefixWord ++ tailWord_8370764) baseStart_8370764 baseEnd_8370764 := by
    simpa [prefixWord, tailWord_8370764, baseEnd_8370764] using wordTrace_append hprefix tailTrace_8370764
  have hstable : (prefixWord ++ tailWord_8370764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370764).length < 2 ^ (prefixWord ++ tailWord_8370764).sum := by decide
  have hdescent : baseEnd_8370764 < baseStart_8370764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370792 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_8370792 : Nat := 118140960795 + 8370792 * 2 ^ 59
def prefixEnd_8370792 : Nat := 4983230072969 + 3 ^ 40 * 8370792 * 2
def baseEnd_8370792 : Nat := 4298239754810718471503435

theorem tailTrace_8370792 : CollatzResearch.WordTrace tailWord_8370792 prefixEnd_8370792 4298239754810718471503435 := by
  unfold tailWord_8370792
  simp only [CollatzResearch.WordTrace]
  refine ⟨152653933145028838150525315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203538577526705117534033753 152653933145028838150525315)
  ·
    refine ⟨228980899717543257225787973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152653933145028838150525315 228980899717543257225787973)
    ·
      refine ⟨42933918697039360729835245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228980899717543257225787973 42933918697039360729835245)
      ·
        refine ⟨16100219511389760273688217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42933918697039360729835245 16100219511389760273688217)
        ·
          refine ⟨12075164633542320205266163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16100219511389760273688217 12075164633542320205266163)
          ·
            refine ⟨18112746950313480307899245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075164633542320205266163 18112746950313480307899245)
            ·
              refine ⟨6792280106367555115462217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18112746950313480307899245 6792280106367555115462217)
              ·
                refine ⟨5094210079775666336596663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792280106367555115462217 5094210079775666336596663)
                ·
                  refine ⟨7641315119663499504894995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094210079775666336596663 7641315119663499504894995)
                  ·
                    refine ⟨11461972679495249257342493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641315119663499504894995 11461972679495249257342493)
                    ·
                      refine ⟨4298239754810718471503435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11461972679495249257342493 4298239754810718471503435)
                      ·
                        rfl

theorem cell23_8370792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_8370792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370792 prefixEnd_8370792 := by exact prefixLift 8370792
  have htrace : WordTrace (prefixWord ++ tailWord_8370792) baseStart_8370792 baseEnd_8370792 := by
    simpa [prefixWord, tailWord_8370792, baseEnd_8370792] using wordTrace_append hprefix tailTrace_8370792
  have hstable : (prefixWord ++ tailWord_8370792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370792).length < 2 ^ (prefixWord ++ tailWord_8370792).sum := by decide
  have hdescent : baseEnd_8370792 < baseStart_8370792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370827 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_8370827 : Nat := 118140960795 + 8370827 * 2 ^ 59
def prefixEnd_8370827 : Nat := 4983230072969 + 3 ^ 40 * 8370827 * 2
def baseEnd_8370827 : Nat := 4298257726633625834565773

theorem tailTrace_8370827 : CollatzResearch.WordTrace tailWord_8370827 prefixEnd_8370827 4298257726633625834565773 := by
  unfold tailWord_8370827
  simp only [CollatzResearch.WordTrace]
  refine ⟨305309142844930877278574735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203539428563287251519049823 305309142844930877278574735)
  ·
    refine ⟨457963714267396315917862103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305309142844930877278574735 457963714267396315917862103)
    ·
      refine ⟨686945571401094473876793155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457963714267396315917862103 686945571401094473876793155)
      ·
        refine ⟨1030418357101641710815189733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686945571401094473876793155 1030418357101641710815189733)
        ·
          refine ⟨193203441956557820777848075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1030418357101641710815189733 193203441956557820777848075)
          ·
            refine ⟨289805162934836731166772113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193203441956557820777848075 289805162934836731166772113)
            ·
              refine ⟨217353872201127548375079085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289805162934836731166772113 217353872201127548375079085)
              ·
                refine ⟨81507702075422830640654657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217353872201127548375079085 81507702075422830640654657)
                ·
                  refine ⟨61130776556567122980490993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81507702075422830640654657 61130776556567122980490993)
                  ·
                    refine ⟨45848082417425342235368245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61130776556567122980490993 45848082417425342235368245)
                    ·
                      refine ⟨4298257726633625834565773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45848082417425342235368245 4298257726633625834565773)
                      ·
                        rfl

theorem cell23_8370827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_8370827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370827 prefixEnd_8370827 := by exact prefixLift 8370827
  have htrace : WordTrace (prefixWord ++ tailWord_8370827) baseStart_8370827 baseEnd_8370827 := by
    simpa [prefixWord, tailWord_8370827, baseEnd_8370827] using wordTrace_append hprefix tailTrace_8370827
  have hstable : (prefixWord ++ tailWord_8370827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370827).length < 2 ^ (prefixWord ++ tailWord_8370827).sum := by decide
  have hdescent : baseEnd_8370827 < baseStart_8370827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370849 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_8370849 : Nat := 118140960795 + 8370849 * 2 ^ 59
def prefixEnd_8370849 : Nat := 4983230072969 + 3 ^ 40 * 8370849 * 2
def baseEnd_8370849 : Nat := 4298269023208024748490673

theorem tailTrace_8370849 : CollatzResearch.WordTrace tailWord_8370849 prefixEnd_8370849 4298269023208024748490673 := by
  unfold tailWord_8370849
  simp only [CollatzResearch.WordTrace]
  refine ⟨305309945250851175035875601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203539963500567450023917067 305309945250851175035875601)
  ·
    refine ⟨228982458938138381276906701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305309945250851175035875601 228982458938138381276906701)
    ·
      refine ⟨85868422101801892978840013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228982458938138381276906701 85868422101801892978840013)
      ·
        refine ⟨32200658288175709867065005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85868422101801892978840013 32200658288175709867065005)
        ·
          refine ⟨12075246858065891200149377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32200658288175709867065005 12075246858065891200149377)
          ·
            refine ⟨9056435143549418400112033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12075246858065891200149377 9056435143549418400112033)
            ·
              refine ⟨6792326357662063800084025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056435143549418400112033 6792326357662063800084025)
              ·
                refine ⟨5094244768246547850063019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792326357662063800084025 5094244768246547850063019)
                ·
                  refine ⟨7641367152369821775094529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094244768246547850063019 7641367152369821775094529)
                  ·
                    refine ⟨5731025364277366331320897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7641367152369821775094529 5731025364277366331320897)
                    ·
                      refine ⟨4298269023208024748490673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731025364277366331320897 4298269023208024748490673)
                      ·
                        rfl

theorem cell23_8370849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_8370849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370849 prefixEnd_8370849 := by exact prefixLift 8370849
  have htrace : WordTrace (prefixWord ++ tailWord_8370849) baseStart_8370849 baseEnd_8370849 := by
    simpa [prefixWord, tailWord_8370849, baseEnd_8370849] using wordTrace_append hprefix tailTrace_8370849
  have hstable : (prefixWord ++ tailWord_8370849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370849).length < 2 ^ (prefixWord ++ tailWord_8370849).sum := by decide
  have hdescent : baseEnd_8370849 < baseStart_8370849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370857 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_8370857 : Nat := 118140960795 + 8370857 * 2 ^ 59
def prefixEnd_8370857 : Nat := 4983230072969 + 3 ^ 40 * 8370857 * 2
def baseEnd_8370857 : Nat := 4298273131053260717190635

theorem tailTrace_8370857 : CollatzResearch.WordTrace tailWord_8370857 prefixEnd_8370857 4298273131053260717190635 := by
  unfold tailWord_8370857
  simp only [CollatzResearch.WordTrace]
  refine ⟨305310237034822192402166825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203540158023214794934777883 305310237034822192402166825)
  ·
    refine ⟨228982677776116644301625119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305310237034822192402166825 228982677776116644301625119)
    ·
      refine ⟨343474016664174966452437679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228982677776116644301625119 343474016664174966452437679)
      ·
        refine ⟨515211024996262449678656519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343474016664174966452437679 515211024996262449678656519)
        ·
          refine ⟨772816537494393674517984779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515211024996262449678656519 772816537494393674517984779)
          ·
            refine ⟨1159224806241590511776977169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772816537494393674517984779 1159224806241590511776977169)
            ·
              refine ⟨869418604681192883832732877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159224806241590511776977169 869418604681192883832732877)
              ·
                refine ⟨326031976755447331437274829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869418604681192883832732877 326031976755447331437274829)
                ·
                  refine ⟨122261991283292749288978061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326031976755447331437274829 122261991283292749288978061)
                  ·
                    refine ⟨45848246731234780983366773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122261991283292749288978061 45848246731234780983366773)
                    ·
                      refine ⟨4298273131053260717190635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45848246731234780983366773 4298273131053260717190635)
                      ·
                        rfl

theorem cell23_8370857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_8370857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370857 prefixEnd_8370857 := by exact prefixLift 8370857
  have htrace : WordTrace (prefixWord ++ tailWord_8370857) baseStart_8370857 baseEnd_8370857 := by
    simpa [prefixWord, tailWord_8370857, baseEnd_8370857] using wordTrace_append hprefix tailTrace_8370857
  have hstable : (prefixWord ++ tailWord_8370857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370857).length < 2 ^ (prefixWord ++ tailWord_8370857).sum := by decide
  have hdescent : baseEnd_8370857 < baseStart_8370857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370874 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_8370874 : Nat := 118140960795 + 8370874 * 2 ^ 59
def prefixEnd_8370874 : Nat := 4983230072969 + 3 ^ 40 * 8370874 * 2
def baseEnd_8370874 : Nat := 4298281860224387150678057

theorem tailTrace_8370874 : CollatzResearch.WordTrace tailWord_8370874 prefixEnd_8370874 4298281860224387150678057 := by
  unfold tailWord_8370874
  simp only [CollatzResearch.WordTrace]
  refine ⟨76327714268940151076383919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203540571383840402870357117 76327714268940151076383919)
  ·
    refine ⟨114491571403410226614575879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76327714268940151076383919 114491571403410226614575879)
    ·
      refine ⟨171737357105115339921863819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114491571403410226614575879 171737357105115339921863819)
      ·
        refine ⟨257606035657673009882795729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171737357105115339921863819 257606035657673009882795729)
        ·
          refine ⟨193204526743254757412096797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257606035657673009882795729 193204526743254757412096797)
          ·
            refine ⟨72451697528720534029536299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193204526743254757412096797 72451697528720534029536299)
            ·
              refine ⟨108677546293080801044304449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72451697528720534029536299 108677546293080801044304449)
              ·
                refine ⟨81508159719810600783228337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108677546293080801044304449 81508159719810600783228337)
                ·
                  refine ⟨61131119789857950587421253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81508159719810600783228337 61131119789857950587421253)
                  ·
                    refine ⟨11462084960598365735141485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61131119789857950587421253 11462084960598365735141485)
                    ·
                      refine ⟨4298281860224387150678057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462084960598365735141485 4298281860224387150678057)
                      ·
                        rfl

theorem cell23_8370874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_8370874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370874 prefixEnd_8370874 := by exact prefixLift 8370874
  have htrace : WordTrace (prefixWord ++ tailWord_8370874) baseStart_8370874 baseEnd_8370874 := by
    simpa [prefixWord, tailWord_8370874, baseEnd_8370874] using wordTrace_append hprefix tailTrace_8370874
  have hstable : (prefixWord ++ tailWord_8370874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370874).length < 2 ^ (prefixWord ++ tailWord_8370874).sum := by decide
  have hdescent : baseEnd_8370874 < baseStart_8370874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370886 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_8370886 : Nat := 118140960795 + 8370886 * 2 ^ 59
def prefixEnd_8370886 : Nat := 4983230072969 + 3 ^ 40 * 8370886 * 2
def baseEnd_8370886 : Nat := 4298288021992241103728003

theorem tailTrace_8370886 : CollatzResearch.WordTrace tailWord_8370886 prefixEnd_8370886 4298288021992241103728003 := by
  unfold tailWord_8370886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540977960991160323592891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203540863167811420236648341 9540977960991160323592891)
  ·
    refine ⟨14311466941486740485389337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9540977960991160323592891 14311466941486740485389337)
    ·
      refine ⟨10733600206115055364042003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14311466941486740485389337 10733600206115055364042003)
      ·
        refine ⟨16100400309172583046063005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733600206115055364042003 16100400309172583046063005)
        ·
          refine ⟨6037650115939718642273627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16100400309172583046063005 6037650115939718642273627)
          ·
            refine ⟨9056475173909577963410441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037650115939718642273627 9056475173909577963410441)
            ·
              refine ⟨6792356380432183472557831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056475173909577963410441 6792356380432183472557831)
              ·
                refine ⟨10188534570648275208836747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792356380432183472557831 10188534570648275208836747)
                ·
                  refine ⟨15282801855972412813255121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188534570648275208836747 15282801855972412813255121)
                  ·
                    refine ⟨11462101391979309609941341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15282801855972412813255121 11462101391979309609941341)
                    ·
                      refine ⟨4298288021992241103728003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462101391979309609941341 4298288021992241103728003)
                      ·
                        rfl

theorem cell23_8370886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_8370886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370886 prefixEnd_8370886 := by exact prefixLift 8370886
  have htrace : WordTrace (prefixWord ++ tailWord_8370886) baseStart_8370886 baseEnd_8370886 := by
    simpa [prefixWord, tailWord_8370886, baseEnd_8370886] using wordTrace_append hprefix tailTrace_8370886
  have hstable : (prefixWord ++ tailWord_8370886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370886).length < 2 ^ (prefixWord ++ tailWord_8370886).sum := by decide
  have hdescent : baseEnd_8370886 < baseStart_8370886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370892 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_8370892 : Nat := 118140960795 + 8370892 * 2 ^ 59
def prefixEnd_8370892 : Nat := 4983230072969 + 3 ^ 40 * 8370892 * 2
def baseEnd_8370892 : Nat := 4298291102876168080252975

theorem tailTrace_8370892 : CollatzResearch.WordTrace tailWord_8370892 prefixEnd_8370892 4298291102876168080252975 := by
  unfold tailWord_8370892
  simp only [CollatzResearch.WordTrace]
  refine ⟨152655756794847696689845465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203541009059796928919793953 152655756794847696689845465)
  ·
    refine ⟨114491817596135772517384099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152655756794847696689845465 114491817596135772517384099)
    ·
      refine ⟨171737726394203658776076149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114491817596135772517384099 171737726394203658776076149)
      ·
        refine ⟨16100411849456593010257139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171737726394203658776076149 16100411849456593010257139)
        ·
          refine ⟨24150617774184889515385709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100411849456593010257139 24150617774184889515385709)
          ·
            refine ⟨9056481665319333568269641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24150617774184889515385709 9056481665319333568269641)
            ·
              refine ⟨6792361248989500176202231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056481665319333568269641 6792361248989500176202231)
              ·
                refine ⟨10188541873484250264303347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792361248989500176202231 10188541873484250264303347)
                ·
                  refine ⟨15282812810226375396455021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188541873484250264303347 15282812810226375396455021)
                  ·
                    refine ⟨5731054803834890773670633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15282812810226375396455021 5731054803834890773670633)
                    ·
                      refine ⟨4298291102876168080252975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731054803834890773670633 4298291102876168080252975)
                      ·
                        rfl

theorem cell23_8370892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_8370892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370892 prefixEnd_8370892 := by exact prefixLift 8370892
  have htrace : WordTrace (prefixWord ++ tailWord_8370892) baseStart_8370892 baseEnd_8370892 := by
    simpa [prefixWord, tailWord_8370892, baseEnd_8370892] using wordTrace_append hprefix tailTrace_8370892
  have hstable : (prefixWord ++ tailWord_8370892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370892).length < 2 ^ (prefixWord ++ tailWord_8370892).sum := by decide
  have hdescent : baseEnd_8370892 < baseStart_8370892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370907 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 11]
def baseStart_8370907 : Nat := 118140960795 + 8370907 * 2 ^ 59
def prefixEnd_8370907 : Nat := 4983230072969 + 3 ^ 40 * 8370907 * 2
def baseEnd_8370907 : Nat := 1432766268361995173855135

theorem tailTrace_8370907 : CollatzResearch.WordTrace tailWord_8370907 prefixEnd_8370907 1432766268361995173855135 := by
  unfold tailWord_8370907
  simp only [CollatzResearch.WordTrace]
  refine ⟨305312060684641050941486975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203541373789760700627657983 305312060684641050941486975)
  ·
    refine ⟨457968091026961576412230463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305312060684641050941486975 457968091026961576412230463)
    ·
      refine ⟨686952136540442364618345695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457968091026961576412230463 686952136540442364618345695)
      ·
        refine ⟨1030428204810663546927518543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686952136540442364618345695 1030428204810663546927518543)
        ·
          refine ⟨1545642307215995320391277815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030428204810663546927518543 1545642307215995320391277815)
          ·
            refine ⟨2318463460823992980586916723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545642307215995320391277815 2318463460823992980586916723)
            ·
              refine ⟨3477695191235989470880375085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318463460823992980586916723 3477695191235989470880375085)
              ·
                refine ⟨1304135696713496051580140657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3477695191235989470880375085 1304135696713496051580140657)
                ·
                  refine ⟨978101772535122038685105493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304135696713496051580140657 978101772535122038685105493)
                  ·
                    refine ⟨1432766268361995173855135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 978101772535122038685105493 1432766268361995173855135)
                    ·
                      rfl

theorem cell23_8370907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_8370907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370907 prefixEnd_8370907 := by exact prefixLift 8370907
  have htrace : WordTrace (prefixWord ++ tailWord_8370907) baseStart_8370907 baseEnd_8370907 := by
    simpa [prefixWord, tailWord_8370907, baseEnd_8370907] using wordTrace_append hprefix tailTrace_8370907
  have hstable : (prefixWord ++ tailWord_8370907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370907).length < 2 ^ (prefixWord ++ tailWord_8370907).sum := by decide
  have hdescent : baseEnd_8370907 < baseStart_8370907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370911 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 5]
def baseStart_8370911 : Nat := 118140960795 + 8370911 * 2 ^ 59
def prefixEnd_8370911 : Nat := 4983230072969 + 3 ^ 40 * 8370911 * 2
def baseEnd_8370911 : Nat := 477588984334289278435043

theorem tailTrace_8370911 : CollatzResearch.WordTrace tailWord_8370911 prefixEnd_8370911 477588984334289278435043 := by
  unfold tailWord_8370911
  simp only [CollatzResearch.WordTrace]
  refine ⟨305312206576626559624632587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203541471051084373083088391 305312206576626559624632587)
  ·
    refine ⟨457968309864939839436948881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305312206576626559624632587 457968309864939839436948881)
    ·
      refine ⟨343476232398704879577711661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457968309864939839436948881 343476232398704879577711661)
      ·
        refine ⟨128803587149514329841641873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343476232398704879577711661 128803587149514329841641873)
        ·
          refine ⟨96602690362135747381231405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128803587149514329841641873 96602690362135747381231405)
          ·
            refine ⟨36226008885800905267961777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96602690362135747381231405 36226008885800905267961777)
            ·
              refine ⟨27169506664350678950971333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36226008885800905267961777 27169506664350678950971333)
              ·
                refine ⟨5094282499565752303307125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27169506664350678950971333 5094282499565752303307125)
                ·
                  refine ⟨477588984334289278435043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5094282499565752303307125 477588984334289278435043)
                  ·
                    rfl

theorem cell23_8370911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 5].length) (baseStart_8370911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370911 prefixEnd_8370911 := by exact prefixLift 8370911
  have htrace : WordTrace (prefixWord ++ tailWord_8370911) baseStart_8370911 baseEnd_8370911 := by
    simpa [prefixWord, tailWord_8370911, baseEnd_8370911] using wordTrace_append hprefix tailTrace_8370911
  have hstable : (prefixWord ++ tailWord_8370911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370911).length < 2 ^ (prefixWord ++ tailWord_8370911).sum := by decide
  have hdescent : baseEnd_8370911 < baseStart_8370911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370961 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_8370961 : Nat := 118140960795 + 8370961 * 2 ^ 59
def prefixEnd_8370961 : Nat := 4983230072969 + 3 ^ 40 * 8370961 * 2
def baseEnd_8370961 : Nat := 4298326533041328310290157

theorem tailTrace_8370961 : CollatzResearch.WordTrace tailWord_8370961 prefixEnd_8370961 4298326533041328310290157 := by
  unfold tailWord_8370961
  simp only [CollatzResearch.WordTrace]
  refine ⟨305314030226445418163952737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203542686817630278775968491 305314030226445418163952737)
  ·
    refine ⟨228985522669834063622964553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305314030226445418163952737 228985522669834063622964553)
    ·
      refine ⟨171739142002375547717223415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228985522669834063622964553 171739142002375547717223415)
      ·
        refine ⟨257608713003563321575835123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171739142002375547717223415 257608713003563321575835123)
        ·
          refine ⟨386413069505344982363752685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257608713003563321575835123 386413069505344982363752685)
          ·
            refine ⟨144904901064504368386407257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386413069505344982363752685 144904901064504368386407257)
            ·
              refine ⟨108678675798378276289805443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144904901064504368386407257 108678675798378276289805443)
              ·
                refine ⟨163018013697567414434708165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108678675798378276289805443 163018013697567414434708165)
                ·
                  refine ⟨30565877568293890206507781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163018013697567414434708165 30565877568293890206507781)
                  ·
                    refine ⟨5731102044055104413720209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30565877568293890206507781 5731102044055104413720209)
                    ·
                      refine ⟨4298326533041328310290157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731102044055104413720209 4298326533041328310290157)
                      ·
                        rfl

theorem cell23_8370961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_8370961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370961 prefixEnd_8370961 := by exact prefixLift 8370961
  have htrace : WordTrace (prefixWord ++ tailWord_8370961) baseStart_8370961 baseEnd_8370961 := by
    simpa [prefixWord, tailWord_8370961, baseEnd_8370961] using wordTrace_append hprefix tailTrace_8370961
  have hstable : (prefixWord ++ tailWord_8370961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370961).length < 2 ^ (prefixWord ++ tailWord_8370961).sum := by decide
  have hdescent : baseEnd_8370961 < baseStart_8370961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370962 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_8370962 : Nat := 118140960795 + 8370962 * 2 ^ 59
def prefixEnd_8370962 : Nat := 4983230072969 + 3 ^ 40 * 8370962 * 2
def baseEnd_8370962 : Nat := 477591894057998089597517

theorem tailTrace_8370962 : CollatzResearch.WordTrace tailWord_8370962 prefixEnd_8370962 477591894057998089597517 := by
  unfold tailWord_8370962
  simp only [CollatzResearch.WordTrace]
  refine ⟨76328516674860448833684785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203542711132961196889826093 76328516674860448833684785)
  ·
    refine ⟨57246387506145336625263589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76328516674860448833684785 57246387506145336625263589)
    ·
      refine ⟨10733697657402250617236923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57246387506145336625263589 10733697657402250617236923)
      ·
        refine ⟨16100546486103375925855385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733697657402250617236923 16100546486103375925855385)
        ·
          refine ⟨12075409864577531944391539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16100546486103375925855385 12075409864577531944391539)
          ·
            refine ⟨18113114796866297916587309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075409864577531944391539 18113114796866297916587309)
            ·
              refine ⟨6792418048824861718720241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18113114796866297916587309 6792418048824861718720241)
              ·
                refine ⟨5094313536618646289040181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792418048824861718720241 5094313536618646289040181)
                ·
                  refine ⟨477591894057998089597517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5094313536618646289040181 477591894057998089597517)
                  ·
                    rfl

theorem cell23_8370962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_8370962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370962 prefixEnd_8370962 := by exact prefixLift 8370962
  have htrace : WordTrace (prefixWord ++ tailWord_8370962) baseStart_8370962 baseEnd_8370962 := by
    simpa [prefixWord, tailWord_8370962, baseEnd_8370962] using wordTrace_append hprefix tailTrace_8370962
  have hstable : (prefixWord ++ tailWord_8370962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370962).length < 2 ^ (prefixWord ++ tailWord_8370962).sum := by decide
  have hdescent : baseEnd_8370962 < baseStart_8370962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8370981 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_8370981 : Nat := 118140960795 + 8370981 * 2 ^ 59
def prefixEnd_8370981 : Nat := 4983230072969 + 3 ^ 40 * 8370981 * 2
def baseEnd_8370981 : Nat := 4298336802654418232040065

theorem tailTrace_8370981 : CollatzResearch.WordTrace tailWord_8370981 prefixEnd_8370981 4298336802654418232040065 := by
  unfold tailWord_8370981
  simp only [CollatzResearch.WordTrace]
  refine ⟨305314759686372961579680797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203543173124248641053120531 305314759686372961579680797)
  ·
    refine ⟨114493034882389860592380299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305314759686372961579680797 114493034882389860592380299)
    ·
      refine ⟨171739552323584790888570449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114493034882389860592380299 171739552323584790888570449)
      ·
        refine ⟨128804664242688593166427837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171739552323584790888570449 128804664242688593166427837)
        ·
          refine ⟨48301749091008222437410439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128804664242688593166427837 48301749091008222437410439)
          ·
            refine ⟨72452623636512333656115659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48301749091008222437410439 72452623636512333656115659)
            ·
              refine ⟨108678935454768500484173489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72452623636512333656115659 108678935454768500484173489)
              ·
                refine ⟨81509201591076375363130117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108678935454768500484173489 81509201591076375363130117)
                ·
                  refine ⟨15282975298326820380586897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81509201591076375363130117 15282975298326820380586897)
                  ·
                    refine ⟨11462231473745115285440173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15282975298326820380586897 11462231473745115285440173)
                    ·
                      refine ⟨4298336802654418232040065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462231473745115285440173 4298336802654418232040065)
                      ·
                        rfl

theorem cell23_8370981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_8370981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8370981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8370981 prefixEnd_8370981 := by exact prefixLift 8370981
  have htrace : WordTrace (prefixWord ++ tailWord_8370981) baseStart_8370981 baseEnd_8370981 := by
    simpa [prefixWord, tailWord_8370981, baseEnd_8370981] using wordTrace_append hprefix tailTrace_8370981
  have hstable : (prefixWord ++ tailWord_8370981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8370981).length < 2 ^ (prefixWord ++ tailWord_8370981).sum := by decide
  have hdescent : baseEnd_8370981 < baseStart_8370981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8370981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371004 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_8371004 : Nat := 118140960795 + 8371004 * 2 ^ 59
def prefixEnd_8371004 : Nat := 4983230072969 + 3 ^ 40 * 8371004 * 2
def baseEnd_8371004 : Nat := 4298348612709471642052459

theorem tailTrace_8371004 : CollatzResearch.WordTrace tailWord_8371004 prefixEnd_8371004 4298348612709471642052459 := by
  unfold tailWord_8371004
  simp only [CollatzResearch.WordTrace]
  refine ⟨152657799282644818253884033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203543732376859757671845377 152657799282644818253884033)
  ·
    refine ⟨114493349461983613690413025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152657799282644818253884033 114493349461983613690413025)
    ·
      refine ⟨85870012096487710267809769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114493349461983613690413025 85870012096487710267809769)
      ·
        refine ⟨64402509072365782700857327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85870012096487710267809769 64402509072365782700857327)
        ·
          refine ⟨96603763608548674051285991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64402509072365782700857327 96603763608548674051285991)
          ·
            refine ⟨144905645412823011076928987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96603763608548674051285991 144905645412823011076928987)
            ·
              refine ⟨217358468119234516615393481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144905645412823011076928987 217358468119234516615393481)
              ·
                refine ⟨163018851089425887461545111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217358468119234516615393481 163018851089425887461545111)
                ·
                  refine ⟨244528276634138831192317667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163018851089425887461545111 244528276634138831192317667)
                  ·
                    refine ⟨366792414951208246788476501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244528276634138831192317667 366792414951208246788476501)
                    ·
                      refine ⟨4298348612709471642052459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 366792414951208246788476501 4298348612709471642052459)
                      ·
                        rfl

theorem cell23_8371004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_8371004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371004 prefixEnd_8371004 := by exact prefixLift 8371004
  have htrace : WordTrace (prefixWord ++ tailWord_8371004) baseStart_8371004 baseEnd_8371004 := by
    simpa [prefixWord, tailWord_8371004, baseEnd_8371004] using wordTrace_append hprefix tailTrace_8371004
  have hstable : (prefixWord ++ tailWord_8371004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371004).length < 2 ^ (prefixWord ++ tailWord_8371004).sum := by decide
  have hdescent : baseEnd_8371004 < baseStart_8371004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371031 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 3, 5]
def baseStart_8371031 : Nat := 118140960795 + 8371031 * 2 ^ 59
def prefixEnd_8371031 : Nat := 4983230072969 + 3 ^ 40 * 8371031 * 2
def baseEnd_8371031 : Nat := 1432787492229047678804945

theorem tailTrace_8371031 : CollatzResearch.WordTrace tailWord_8371031 prefixEnd_8371031 1432787492229047678804945 := by
  unfold tailWord_8371031
  simp only [CollatzResearch.WordTrace]
  refine ⟨305316583336191820119000947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203544388890794546746000631 305316583336191820119000947)
  ·
    refine ⟨457974875004287730178501421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305316583336191820119000947 457974875004287730178501421)
    ·
      refine ⟨171740578126607898816938033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457974875004287730178501421 171740578126607898816938033)
      ·
        refine ⟨128805433594955924112703525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171740578126607898816938033 128805433594955924112703525)
        ·
          refine ⟨24151018799054235771131911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128805433594955924112703525 24151018799054235771131911)
          ·
            refine ⟨36226528198581353656697867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151018799054235771131911 36226528198581353656697867)
            ·
              refine ⟨54339792297872030485046801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36226528198581353656697867 54339792297872030485046801)
              ·
                refine ⟨40754844223404022863785101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54339792297872030485046801 40754844223404022863785101)
                ·
                  refine ⟨15283066583776508573919413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40754844223404022863785101 15283066583776508573919413)
                  ·
                    refine ⟨1432787492229047678804945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15283066583776508573919413 1432787492229047678804945)
                    ·
                      rfl

theorem cell23_8371031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_8371031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371031 prefixEnd_8371031 := by exact prefixLift 8371031
  have htrace : WordTrace (prefixWord ++ tailWord_8371031) baseStart_8371031 baseEnd_8371031 := by
    simpa [prefixWord, tailWord_8371031, baseEnd_8371031] using wordTrace_append hprefix tailTrace_8371031
  have hstable : (prefixWord ++ tailWord_8371031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371031).length < 2 ^ (prefixWord ++ tailWord_8371031).sum := by decide
  have hdescent : baseEnd_8371031 < baseStart_8371031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371051 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4]
def baseStart_8371051 : Nat := 118140960795 + 8371051 * 2 ^ 59
def prefixEnd_8371051 : Nat := 4983230072969 + 3 ^ 40 * 8371051 * 2
def baseEnd_8371051 : Nat := 4298372746300232958164743

theorem tailTrace_8371051 : CollatzResearch.WordTrace tailWord_8371051 prefixEnd_8371051 4298372746300232958164743 := by
  unfold tailWord_8371051
  simp only [CollatzResearch.WordTrace]
  refine ⟨305317312796119363534729007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203544875197412909023152671 305317312796119363534729007)
  ·
    refine ⟨457975969194179045302093511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305317312796119363534729007 457975969194179045302093511)
    ·
      refine ⟨686963953791268567953140267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457975969194179045302093511 686963953791268567953140267)
      ·
        refine ⟨1030445930686902851929710401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686963953791268567953140267 1030445930686902851929710401)
        ·
          refine ⟨772834448015177138947282801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030445930686902851929710401 772834448015177138947282801)
          ·
            refine ⟨579625836011382854210462101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772834448015177138947282801 579625836011382854210462101)
            ·
              refine ⟨27169961063033571291115411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 579625836011382854210462101 27169961063033571291115411)
              ·
                refine ⟨40754941594550356936673117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27169961063033571291115411 40754941594550356936673117)
                ·
                  refine ⟨15283103097956383851252419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40754941594550356936673117 15283103097956383851252419)
                  ·
                    refine ⟨22924654646934575776878629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15283103097956383851252419 22924654646934575776878629)
                    ·
                      refine ⟨4298372746300232958164743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22924654646934575776878629 4298372746300232958164743)
                      ·
                        rfl

theorem cell23_8371051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 4].length) (baseStart_8371051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371051 prefixEnd_8371051 := by exact prefixLift 8371051
  have htrace : WordTrace (prefixWord ++ tailWord_8371051) baseStart_8371051 baseEnd_8371051 := by
    simpa [prefixWord, tailWord_8371051, baseEnd_8371051] using wordTrace_append hprefix tailTrace_8371051
  have hstable : (prefixWord ++ tailWord_8371051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371051).length < 2 ^ (prefixWord ++ tailWord_8371051).sum := by decide
  have hdescent : baseEnd_8371051 < baseStart_8371051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371065 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 1, 5]
def baseStart_8371065 : Nat := 118140960795 + 8371065 * 2 ^ 59
def prefixEnd_8371065 : Nat := 4983230072969 + 3 ^ 40 * 8371065 * 2
def baseEnd_8371065 : Nat := 1432793311676465301129893

theorem tailTrace_8371065 : CollatzResearch.WordTrace tailWord_8371065 prefixEnd_8371065 1432793311676465301129893 := by
  unfold tailWord_8371065
  simp only [CollatzResearch.WordTrace]
  refine ⟨305317823418068643925738649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203545215612045762617159099 305317823418068643925738649)
  ·
    refine ⟨228988367563551482944303987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305317823418068643925738649 228988367563551482944303987)
    ·
      refine ⟨343482551345327224416455981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228988367563551482944303987 343482551345327224416455981)
      ·
        refine ⟨128805956754497709156170993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343482551345327224416455981 128805956754497709156170993)
        ·
          refine ⟨96604467565873281867128245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128805956754497709156170993 96604467565873281867128245)
          ·
            refine ⟨9056668834300620175043273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96604467565873281867128245 9056668834300620175043273)
            ·
              refine ⟨6792501625725465131282455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9056668834300620175043273 6792501625725465131282455)
              ·
                refine ⟨10188752438588197696923683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792501625725465131282455 10188752438588197696923683)
                ·
                  refine ⟨15283128657882296545385525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188752438588197696923683 15283128657882296545385525)
                  ·
                    refine ⟨1432793311676465301129893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15283128657882296545385525 1432793311676465301129893)
                    ·
                      rfl

theorem cell23_8371065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_8371065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371065 prefixEnd_8371065 := by exact prefixLift 8371065
  have htrace : WordTrace (prefixWord ++ tailWord_8371065) baseStart_8371065 baseEnd_8371065 := by
    simpa [prefixWord, tailWord_8371065, baseEnd_8371065] using wordTrace_append hprefix tailTrace_8371065
  have hstable : (prefixWord ++ tailWord_8371065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371065).length < 2 ^ (prefixWord ++ tailWord_8371065).sum := by decide
  have hdescent : baseEnd_8371065 < baseStart_8371065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371095 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 2, 4]
def baseStart_8371095 : Nat := 118140960795 + 8371095 * 2 ^ 59
def prefixEnd_8371095 : Nat := 4983230072969 + 3 ^ 40 * 8371095 * 2
def baseEnd_8371095 : Nat := 1432798446483010262004847

theorem tailTrace_8371095 : CollatzResearch.WordTrace tailWord_8371095 prefixEnd_8371095 1432798446483010262004847 := by
  unfold tailWord_8371095
  simp only [CollatzResearch.WordTrace]
  refine ⟨305318917607959959049330739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203545945071973306032887159 305318917607959959049330739)
  ·
    refine ⟨457978376411939938573996109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305318917607959959049330739 457978376411939938573996109)
    ·
      refine ⟨171741891154477476965248541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457978376411939938573996109 171741891154477476965248541)
      ·
        refine ⟨64403209182929053861968203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171741891154477476965248541 64403209182929053861968203)
        ·
          refine ⟨96604813774393580792952305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64403209182929053861968203 96604813774393580792952305)
          ·
            refine ⟨72453610330795185594714229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96604813774393580792952305 72453610330795185594714229)
            ·
              refine ⟨6792525968512048649504459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72453610330795185594714229 6792525968512048649504459)
              ·
                refine ⟨10188788952768072974256689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792525968512048649504459 10188788952768072974256689)
                ·
                  refine ⟨7641591714576054730692517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10188788952768072974256689 7641591714576054730692517)
                  ·
                    refine ⟨1432798446483010262004847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7641591714576054730692517 1432798446483010262004847)
                    ·
                      rfl

theorem cell23_8371095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_8371095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371095 prefixEnd_8371095 := by exact prefixLift 8371095
  have htrace : WordTrace (prefixWord ++ tailWord_8371095) baseStart_8371095 baseEnd_8371095 := by
    simpa [prefixWord, tailWord_8371095, baseEnd_8371095] using wordTrace_append hprefix tailTrace_8371095
  have hstable : (prefixWord ++ tailWord_8371095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371095).length < 2 ^ (prefixWord ++ tailWord_8371095).sum := by decide
  have hdescent : baseEnd_8371095 < baseStart_8371095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371098 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_8371098 : Nat := 118140960795 + 8371098 * 2 ^ 59
def prefixEnd_8371098 : Nat := 4983230072969 + 3 ^ 40 * 8371098 * 2
def baseEnd_8371098 : Nat := 4298396879890994274277027

theorem tailTrace_8371098 : CollatzResearch.WordTrace tailWord_8371098 prefixEnd_8371098 4298396879890994274277027 := by
  unfold tailWord_8371098
  simp only [CollatzResearch.WordTrace]
  refine ⟨76329756756737272640422487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203546018017966060374459965 76329756756737272640422487)
  ·
    refine ⟨114494635135105908960633731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76329756756737272640422487 114494635135105908960633731)
    ·
      refine ⟨171741952702658863440950597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114494635135105908960633731 171741952702658863440950597)
      ·
        refine ⟨32201616131748536895178237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171741952702658863440950597 32201616131748536895178237)
        ·
          refine ⟨12075606049405701335691839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32201616131748536895178237 12075606049405701335691839)
          ·
            refine ⟨18113409074108552003537759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075606049405701335691839 18113409074108552003537759)
            ·
              refine ⟨27170113611162828005306639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18113409074108552003537759 27170113611162828005306639)
              ·
                refine ⟨40755170416744242007959959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27170113611162828005306639 40755170416744242007959959)
                ·
                  refine ⟨61132755625116363011939939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40755170416744242007959959 61132755625116363011939939)
                  ·
                    refine ⟨91699133437674544517909909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61132755625116363011939939 91699133437674544517909909)
                    ·
                      refine ⟨4298396879890994274277027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91699133437674544517909909 4298396879890994274277027)
                      ·
                        rfl

theorem cell23_8371098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_8371098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371098 prefixEnd_8371098 := by exact prefixLift 8371098
  have htrace : WordTrace (prefixWord ++ tailWord_8371098) baseStart_8371098 baseEnd_8371098 := by
    simpa [prefixWord, tailWord_8371098, baseEnd_8371098] using wordTrace_append hprefix tailTrace_8371098
  have hstable : (prefixWord ++ tailWord_8371098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371098).length < 2 ^ (prefixWord ++ tailWord_8371098).sum := by decide
  have hdescent : baseEnd_8371098 < baseStart_8371098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371105 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_8371105 : Nat := 118140960795 + 8371105 * 2 ^ 59
def prefixEnd_8371105 : Nat := 4983230072969 + 3 ^ 40 * 8371105 * 2
def baseEnd_8371105 : Nat := 4298400474255575746889495

theorem tailTrace_8371105 : CollatzResearch.WordTrace tailWord_8371105 prefixEnd_8371105 4298400474255575746889495 := by
  unfold tailWord_8371105
  simp only [CollatzResearch.WordTrace]
  refine ⟨305319282337923730757194769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203546188225282487171463179 305319282337923730757194769)
  ·
    refine ⟨228989461753442798067896077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305319282337923730757194769 228989461753442798067896077)
    ·
      refine ⟨85871048157541049275461029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228989461753442798067896077 85871048157541049275461029)
      ·
        refine ⟨16100821529538946739148943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85871048157541049275461029 16100821529538946739148943)
        ·
          refine ⟨24151232294308420108723415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100821529538946739148943 24151232294308420108723415)
          ·
            refine ⟨36226848441462630163085123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151232294308420108723415 36226848441462630163085123)
            ·
              refine ⟨54340272662193945244627685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36226848441462630163085123 54340272662193945244627685)
              ·
                refine ⟨10188801124161364733367691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54340272662193945244627685 10188801124161364733367691)
                ·
                  refine ⟨15283201686242047100051537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188801124161364733367691 15283201686242047100051537)
                  ·
                    refine ⟨11462401264681535325038653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15283201686242047100051537 11462401264681535325038653)
                    ·
                      refine ⟨4298400474255575746889495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462401264681535325038653 4298400474255575746889495)
                      ·
                        rfl

theorem cell23_8371105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_8371105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371105 prefixEnd_8371105 := by exact prefixLift 8371105
  have htrace : WordTrace (prefixWord ++ tailWord_8371105) baseStart_8371105 baseEnd_8371105 := by
    simpa [prefixWord, tailWord_8371105, baseEnd_8371105] using wordTrace_append hprefix tailTrace_8371105
  have hstable : (prefixWord ++ tailWord_8371105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371105).length < 2 ^ (prefixWord ++ tailWord_8371105).sum := by decide
  have hdescent : baseEnd_8371105 < baseStart_8371105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371162 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_8371162 : Nat := 118140960795 + 8371162 * 2 ^ 59
def prefixEnd_8371162 : Nat := 4983230072969 + 3 ^ 40 * 8371162 * 2
def baseEnd_8371162 : Nat := 4298429742652882023876733

theorem tailTrace_8371162 : CollatzResearch.WordTrace tailWord_8371162 prefixEnd_8371162 4298429742652882023876733 := by
  unfold tailWord_8371162
  simp only [CollatzResearch.WordTrace]
  refine ⟨76330340324679307373004935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203547574199144819661346493 76330340324679307373004935)
  ·
    refine ⟨114495510487018961059507403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76330340324679307373004935 114495510487018961059507403)
    ·
      refine ⟨171743265730528441589261105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114495510487018961059507403 171743265730528441589261105)
      ·
        refine ⟨128807449297896331191945829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171743265730528441589261105 128807449297896331191945829)
        ·
          refine ⟨24151396743355562098489843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128807449297896331191945829 24151396743355562098489843)
          ·
            refine ⟨36227095115033343147734765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151396743355562098489843 36227095115033343147734765)
            ·
              refine ⟨13585160668137503680400537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36227095115033343147734765 13585160668137503680400537)
              ·
                refine ⟨10188870501103127760300403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13585160668137503680400537 10188870501103127760300403)
                ·
                  refine ⟨15283305751654691640450605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10188870501103127760300403 15283305751654691640450605)
                  ·
                    refine ⟨5731239656870509365168977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15283305751654691640450605 5731239656870509365168977)
                    ·
                      refine ⟨4298429742652882023876733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731239656870509365168977 4298429742652882023876733)
                      ·
                        rfl

theorem cell23_8371162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_8371162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371162 prefixEnd_8371162 := by exact prefixLift 8371162
  have htrace : WordTrace (prefixWord ++ tailWord_8371162) baseStart_8371162 baseEnd_8371162 := by
    simpa [prefixWord, tailWord_8371162, baseEnd_8371162] using wordTrace_append hprefix tailTrace_8371162
  have hstable : (prefixWord ++ tailWord_8371162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371162).length < 2 ^ (prefixWord ++ tailWord_8371162).sum := by decide
  have hdescent : baseEnd_8371162 < baseStart_8371162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371175 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_8371175 : Nat := 118140960795 + 8371175 * 2 ^ 59
def prefixEnd_8371175 : Nat := 4983230072969 + 3 ^ 40 * 8371175 * 2
def baseEnd_8371175 : Nat := 4298436417901390473014173

theorem tailTrace_8371175 : CollatzResearch.WordTrace tailWord_8371175 prefixEnd_8371175 4298436417901390473014173 := by
  unfold tailWord_8371175
  simp only [CollatzResearch.WordTrace]
  refine ⟨305321835447670132712242979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203547890298446755141495319 305321835447670132712242979)
  ·
    refine ⟨457982753171505199068364469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305321835447670132712242979 457982753171505199068364469)
    ·
      refine ⟨42935883109828612412659169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457982753171505199068364469 42935883109828612412659169)
      ·
        refine ⟨32201912332371459309494377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42935883109828612412659169 32201912332371459309494377)
        ·
          refine ⟨24151434249278594482120783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32201912332371459309494377 24151434249278594482120783)
          ·
            refine ⟨36227151373917891723181175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151434249278594482120783 36227151373917891723181175)
            ·
              refine ⟨54340727060876837584771763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36227151373917891723181175 54340727060876837584771763)
              ·
                refine ⟨81511090591315256377157645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54340727060876837584771763 81511090591315256377157645)
                ·
                  refine ⟨30566658971743221141434117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81511090591315256377157645 30566658971743221141434117)
                  ·
                    refine ⟨5731248557201853964018897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30566658971743221141434117 5731248557201853964018897)
                    ·
                      refine ⟨4298436417901390473014173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731248557201853964018897 4298436417901390473014173)
                      ·
                        rfl

theorem cell23_8371175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_8371175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371175 prefixEnd_8371175 := by exact prefixLift 8371175
  have htrace : WordTrace (prefixWord ++ tailWord_8371175) baseStart_8371175 baseEnd_8371175 := by
    simpa [prefixWord, tailWord_8371175, baseEnd_8371175] using wordTrace_append hprefix tailTrace_8371175
  have hstable : (prefixWord ++ tailWord_8371175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371175).length < 2 ^ (prefixWord ++ tailWord_8371175).sum := by decide
  have hdescent : baseEnd_8371175 < baseStart_8371175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371178 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_8371178 : Nat := 118140960795 + 8371178 * 2 ^ 59
def prefixEnd_8371178 : Nat := 4983230072969 + 3 ^ 40 * 8371178 * 2
def baseEnd_8371178 : Nat := 4298437958343353961276659

theorem tailTrace_8371178 : CollatzResearch.WordTrace tailWord_8371178 prefixEnd_8371178 4298437958343353961276659 := by
  unfold tailWord_8371178
  simp only [CollatzResearch.WordTrace]
  refine ⟨76330486216664816056150547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203547963244439509483068125 76330486216664816056150547)
  ·
    refine ⟨114495729324997224084225821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76330486216664816056150547 114495729324997224084225821)
    ·
      refine ⟨42935898496873959031584683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114495729324997224084225821 42935898496873959031584683)
      ·
        refine ⟨64403847745310938547377025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42935898496873959031584683 64403847745310938547377025)
        ·
          refine ⟨48302885808983203910532769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64403847745310938547377025 48302885808983203910532769)
          ·
            refine ⟨36227164356737402932899577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48302885808983203910532769 36227164356737402932899577)
            ·
              refine ⟨27170373267553052199674683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36227164356737402932899577 27170373267553052199674683)
              ·
                refine ⟨40755559901329578299512025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27170373267553052199674683 40755559901329578299512025)
                ·
                  refine ⟨30566669925997183724634019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40755559901329578299512025 30566669925997183724634019)
                  ·
                    refine ⟨45850004888995775586951029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30566669925997183724634019 45850004888995775586951029)
                    ·
                      refine ⟨4298437958343353961276659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45850004888995775586951029 4298437958343353961276659)
                      ·
                        rfl

theorem cell23_8371178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_8371178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371178 prefixEnd_8371178 := by exact prefixLift 8371178
  have htrace : WordTrace (prefixWord ++ tailWord_8371178) baseStart_8371178 baseEnd_8371178 := by
    simpa [prefixWord, tailWord_8371178, baseEnd_8371178] using wordTrace_append hprefix tailTrace_8371178
  have hstable : (prefixWord ++ tailWord_8371178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371178).length < 2 ^ (prefixWord ++ tailWord_8371178).sum := by decide
  have hdescent : baseEnd_8371178 < baseStart_8371178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371202 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_8371202 : Nat := 118140960795 + 8371202 * 2 ^ 59
def prefixEnd_8371202 : Nat := 4983230072969 + 3 ^ 40 * 8371202 * 2
def baseEnd_8371202 : Nat := 1432816760626353955792183

theorem tailTrace_8371202 : CollatzResearch.WordTrace tailWord_8371202 prefixEnd_8371202 1432816760626353955792183 := by
  unfold tailWord_8371202
  simp only [CollatzResearch.WordTrace]
  refine ⟨76330705054643079080868965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203548546812381544215650573 76330705054643079080868965)
  ·
    refine ⟨14312007197745577327662931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76330705054643079080868965 14312007197745577327662931)
    ·
      refine ⟨21468010796618365991494397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14312007197745577327662931 21468010796618365991494397)
      ·
        refine ⟨8050504048731887246810399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21468010796618365991494397 8050504048731887246810399)
        ·
          refine ⟨12075756073097830870215599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050504048731887246810399 12075756073097830870215599)
          ·
            refine ⟨18113634109646746305323399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12075756073097830870215599 18113634109646746305323399)
            ·
              refine ⟨27170451164470119457985099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18113634109646746305323399 27170451164470119457985099)
              ·
                refine ⟨40755676746705179186977649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27170451164470119457985099 40755676746705179186977649)
                ·
                  refine ⟨30566757560028884390233237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40755676746705179186977649 30566757560028884390233237)
                  ·
                    refine ⟨1432816760626353955792183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30566757560028884390233237 1432816760626353955792183)
                    ·
                      rfl

theorem cell23_8371202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_8371202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371202 prefixEnd_8371202 := by exact prefixLift 8371202
  have htrace : WordTrace (prefixWord ++ tailWord_8371202) baseStart_8371202 baseEnd_8371202 := by
    simpa [prefixWord, tailWord_8371202, baseEnd_8371202] using wordTrace_append hprefix tailTrace_8371202
  have hstable : (prefixWord ++ tailWord_8371202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371202).length < 2 ^ (prefixWord ++ tailWord_8371202).sum := by decide
  have hdescent : baseEnd_8371202 < baseStart_8371202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371208 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_8371208 : Nat := 118140960795 + 8371208 * 2 ^ 59
def prefixEnd_8371208 : Nat := 4983230072969 + 3 ^ 40 * 8371208 * 2
def baseEnd_8371208 : Nat := 4298453362762988843901521

theorem tailTrace_8371208 : CollatzResearch.WordTrace tailWord_8371208 prefixEnd_8371208 4298453362762988843901521 := by
  unfold tailWord_8371208
  simp only [CollatzResearch.WordTrace]
  refine ⟨152661519528275289674097139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203548692704367052898796185 152661519528275289674097139)
  ·
    refine ⟨228992279292412934511145709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152661519528275289674097139 228992279292412934511145709)
    ·
      refine ⟨85872104734654850441679641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228992279292412934511145709 85872104734654850441679641)
      ·
        refine ⟨64404078550991137831259731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85872104734654850441679641 64404078550991137831259731)
        ·
          refine ⟨96606117826486706746889597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64404078550991137831259731 96606117826486706746889597)
          ·
            refine ⟨36227294184932515030083599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96606117826486706746889597 36227294184932515030083599)
            ·
              refine ⟨54340941277398772545125399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36227294184932515030083599 54340941277398772545125399)
              ·
                refine ⟨81511411916098158817688099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54340941277398772545125399 81511411916098158817688099)
                ·
                  refine ⟨122267117874147238226532149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81511411916098158817688099 122267117874147238226532149)
                  ·
                    refine ⟨11462542300701303583737389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122267117874147238226532149 11462542300701303583737389)
                    ·
                      refine ⟨4298453362762988843901521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462542300701303583737389 4298453362762988843901521)
                      ·
                        rfl

theorem cell23_8371208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_8371208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371208 prefixEnd_8371208 := by exact prefixLift 8371208
  have htrace : WordTrace (prefixWord ++ tailWord_8371208) baseStart_8371208 baseEnd_8371208 := by
    simpa [prefixWord, tailWord_8371208, baseEnd_8371208] using wordTrace_append hprefix tailTrace_8371208
  have hstable : (prefixWord ++ tailWord_8371208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371208).length < 2 ^ (prefixWord ++ tailWord_8371208).sum := by decide
  have hdescent : baseEnd_8371208 < baseStart_8371208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371248 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_8371248 : Nat := 118140960795 + 8371248 * 2 ^ 59
def prefixEnd_8371248 : Nat := 4983230072969 + 3 ^ 40 * 8371248 * 2
def baseEnd_8371248 : Nat := 4298473901989168687401337

theorem tailTrace_8371248 : CollatzResearch.WordTrace tailWord_8371248 prefixEnd_8371248 4298473901989168687401337 := by
  unfold tailWord_8371248
  simp only [CollatzResearch.WordTrace]
  refine ⟨152662248988202833089825199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203549665317603777453100265 152662248988202833089825199)
  ·
    refine ⟨228993373482304249634737799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152662248988202833089825199 228993373482304249634737799)
    ·
      refine ⟨343490060223456374452106699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228993373482304249634737799 343490060223456374452106699)
      ·
        refine ⟨515235090335184561678160049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343490060223456374452106699 515235090335184561678160049)
        ·
          refine ⟨386426317751388421258620037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515235090335184561678160049 386426317751388421258620037)
          ·
            refine ⟨72454934578385328985991257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386426317751388421258620037 72454934578385328985991257)
            ·
              refine ⟨54341200933788996739493443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72454934578385328985991257 54341200933788996739493443)
              ·
                refine ⟨81511801400683495109240165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54341200933788996739493443 81511801400683495109240165)
                ·
                  refine ⟨15283462762628155332982531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81511801400683495109240165 15283462762628155332982531)
                  ·
                    refine ⟨22925194143942232999473797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15283462762628155332982531 22925194143942232999473797)
                    ·
                      refine ⟨4298473901989168687401337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22925194143942232999473797 4298473901989168687401337)
                      ·
                        rfl

theorem cell23_8371248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_8371248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371248 prefixEnd_8371248 := by exact prefixLift 8371248
  have htrace : WordTrace (prefixWord ++ tailWord_8371248) baseStart_8371248 baseEnd_8371248 := by
    simpa [prefixWord, tailWord_8371248, baseEnd_8371248] using wordTrace_append hprefix tailTrace_8371248
  have hstable : (prefixWord ++ tailWord_8371248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371248).length < 2 ^ (prefixWord ++ tailWord_8371248).sum := by decide
  have hdescent : baseEnd_8371248 < baseStart_8371248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371278 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_8371278 : Nat := 118140960795 + 8371278 * 2 ^ 59
def prefixEnd_8371278 : Nat := 4983230072969 + 3 ^ 40 * 8371278 * 2
def baseEnd_8371278 : Nat := 4298489306408803570026199

theorem tailTrace_8371278 : CollatzResearch.WordTrace tailWord_8371278 prefixEnd_8371278 4298489306408803570026199 := by
  unfold tailWord_8371278
  simp only [CollatzResearch.WordTrace]
  refine ⟨38165699020787122662905311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203550394777531320868828325 38165699020787122662905311)
  ·
    refine ⟨57248548531180683994357967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38165699020787122662905311 57248548531180683994357967)
    ·
      refine ⟨85872822796771025991536951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57248548531180683994357967 85872822796771025991536951)
      ·
        refine ⟨128809234195156538987305427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85872822796771025991536951 128809234195156538987305427)
        ·
          refine ⟨193213851292734808480958141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128809234195156538987305427 193213851292734808480958141)
          ·
            refine ⟨72455194234775553180359303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193213851292734808480958141 72455194234775553180359303)
            ·
              refine ⟨108682791352163329770538955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72455194234775553180359303 108682791352163329770538955)
              ·
                refine ⟨163024187028244994655808433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108682791352163329770538955 163024187028244994655808433)
                ·
                  refine ⟨122268140271183745991856325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163024187028244994655808433 122268140271183745991856325)
                  ·
                    refine ⟨22925276300846952373473061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122268140271183745991856325 22925276300846952373473061)
                    ·
                      refine ⟨4298489306408803570026199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22925276300846952373473061 4298489306408803570026199)
                      ·
                        rfl

theorem cell23_8371278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_8371278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371278 prefixEnd_8371278 := by exact prefixLift 8371278
  have htrace : WordTrace (prefixWord ++ tailWord_8371278) baseStart_8371278 baseEnd_8371278 := by
    simpa [prefixWord, tailWord_8371278, baseEnd_8371278] using wordTrace_append hprefix tailTrace_8371278
  have hstable : (prefixWord ++ tailWord_8371278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371278).length < 2 ^ (prefixWord ++ tailWord_8371278).sum := by decide
  have hdescent : baseEnd_8371278 < baseStart_8371278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371285 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_8371285 : Nat := 118140960795 + 8371285 * 2 ^ 59
def prefixEnd_8371285 : Nat := 4983230072969 + 3 ^ 40 * 8371285 * 2
def baseEnd_8371285 : Nat := 4298492900773385042638667

theorem tailTrace_8371285 : CollatzResearch.WordTrace tailWord_8371285 prefixEnd_8371285 4298492900773385042638667 := by
  unfold tailWord_8371285
  simp only [CollatzResearch.WordTrace]
  refine ⟨305325847477271621498747309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203550564984847747665831539 305325847477271621498747309)
  ·
    refine ⟨114497192803976858062030241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305325847477271621498747309 114497192803976858062030241)
    ·
      refine ⟨85872894602982643546522681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114497192803976858062030241 85872894602982643546522681)
      ·
        refine ⟨64404670952236982659892011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85872894602982643546522681 64404670952236982659892011)
        ·
          refine ⟨96607006428355473989838017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64404670952236982659892011 96607006428355473989838017)
          ·
            refine ⟨72455254821266605492378513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96607006428355473989838017 72455254821266605492378513)
            ·
              refine ⟨54341441115949954119283885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72455254821266605492378513 54341441115949954119283885)
              ·
                refine ⟨20378040418481232794731457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54341441115949954119283885 20378040418481232794731457)
                ·
                  refine ⟨15283530313860924596048593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20378040418481232794731457 15283530313860924596048593)
                  ·
                    refine ⟨11462647735395693447036445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15283530313860924596048593 11462647735395693447036445)
                    ·
                      refine ⟨4298492900773385042638667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462647735395693447036445 4298492900773385042638667)
                      ·
                        rfl

theorem cell23_8371285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_8371285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371285 prefixEnd_8371285 := by exact prefixLift 8371285
  have htrace : WordTrace (prefixWord ++ tailWord_8371285) baseStart_8371285 baseEnd_8371285 := by
    simpa [prefixWord, tailWord_8371285, baseEnd_8371285] using wordTrace_append hprefix tailTrace_8371285
  have hstable : (prefixWord ++ tailWord_8371285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371285).length < 2 ^ (prefixWord ++ tailWord_8371285).sum := by decide
  have hdescent : baseEnd_8371285 < baseStart_8371285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371375 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_8371375 : Nat := 118140960795 + 8371375 * 2 ^ 59
def prefixEnd_8371375 : Nat := 4983230072969 + 3 ^ 40 * 8371375 * 2
def baseEnd_8371375 : Nat := 4298539114032289690513253

theorem tailTrace_8371375 : CollatzResearch.WordTrace tailWord_8371375 prefixEnd_8371375 4298539114032289690513253 := by
  unfold tailWord_8371375
  simp only [CollatzResearch.WordTrace]
  refine ⟨305329130046945566869523579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203552753364630377913015719 305329130046945566869523579)
  ·
    refine ⟨457993695070418350304285369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305329130046945566869523579 457993695070418350304285369)
    ·
      refine ⟨343495271302813762728214027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457993695070418350304285369 343495271302813762728214027)
      ·
        refine ⟨515242906954220644092321041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343495271302813762728214027 515242906954220644092321041)
        ·
          refine ⟨386432180215665483069240781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515242906954220644092321041 386432180215665483069240781)
          ·
            refine ⟨144912067580874556150965293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386432180215665483069240781 144912067580874556150965293)
            ·
              refine ⟨54342025342827958556611985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144912067580874556150965293 54342025342827958556611985)
              ·
                refine ⟨40756519007120968917458989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54342025342827958556611985 40756519007120968917458989)
                ·
                  refine ⟨15283694627670363344047121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40756519007120968917458989 15283694627670363344047121)
                  ·
                    refine ⟨11462770970752772508035341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15283694627670363344047121 11462770970752772508035341)
                    ·
                      refine ⟨4298539114032289690513253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462770970752772508035341 4298539114032289690513253)
                      ·
                        rfl

theorem cell23_8371375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_8371375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371375 prefixEnd_8371375 := by exact prefixLift 8371375
  have htrace : WordTrace (prefixWord ++ tailWord_8371375) baseStart_8371375 baseEnd_8371375 := by
    simpa [prefixWord, tailWord_8371375, baseEnd_8371375] using wordTrace_append hprefix tailTrace_8371375
  have hstable : (prefixWord ++ tailWord_8371375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371375).length < 2 ^ (prefixWord ++ tailWord_8371375).sum := by decide
  have hdescent : baseEnd_8371375 < baseStart_8371375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371385 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_8371385 : Nat := 118140960795 + 8371385 * 2 ^ 59
def prefixEnd_8371385 : Nat := 4983230072969 + 3 ^ 40 * 8371385 * 2
def baseEnd_8371385 : Nat := 4298544248838834651388207

theorem tailTrace_8371385 : CollatzResearch.WordTrace tailWord_8371385 prefixEnd_8371385 4298544248838834651388207 := by
  unfold tailWord_8371385
  simp only [CollatzResearch.WordTrace]
  refine ⟨305329494776909338577387609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203552996517939559051591739 305329494776909338577387609)
  ·
    refine ⟨228997121082682003933040707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305329494776909338577387609 228997121082682003933040707)
    ·
      refine ⟨343495681624023005899561061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228997121082682003933040707 343495681624023005899561061)
      ·
        refine ⟨64405440304504313606167699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343495681624023005899561061 64405440304504313606167699)
        ·
          refine ⟨96608160456756470409251549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64405440304504313606167699 96608160456756470409251549)
          ·
            refine ⟨36228060171283676403469331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96608160456756470409251549 36228060171283676403469331)
            ·
              refine ⟨54342090256925514605203997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36228060171283676403469331 54342090256925514605203997)
              ·
                refine ⟨20378283846347067976951499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54342090256925514605203997 20378283846347067976951499)
                ·
                  refine ⟨30567425769520601965427249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20378283846347067976951499 30567425769520601965427249)
                  ·
                    refine ⟨22925569327140451474070437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30567425769520601965427249 22925569327140451474070437)
                    ·
                      refine ⟨4298544248838834651388207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22925569327140451474070437 4298544248838834651388207)
                      ·
                        rfl

theorem cell23_8371385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_8371385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371385 prefixEnd_8371385 := by exact prefixLift 8371385
  have htrace : WordTrace (prefixWord ++ tailWord_8371385) baseStart_8371385 baseEnd_8371385 := by
    simpa [prefixWord, tailWord_8371385, baseEnd_8371385] using wordTrace_append hprefix tailTrace_8371385
  have hstable : (prefixWord ++ tailWord_8371385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371385).length < 2 ^ (prefixWord ++ tailWord_8371385).sum := by decide
  have hdescent : baseEnd_8371385 < baseStart_8371385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371406 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_8371406 : Nat := 118140960795 + 8371406 * 2 ^ 59
def prefixEnd_8371406 : Nat := 4983230072969 + 3 ^ 40 * 8371406 * 2
def baseEnd_8371406 : Nat := 4298555031932579069225611

theorem tailTrace_8371406 : CollatzResearch.WordTrace tailWord_8371406 prefixEnd_8371406 4298555031932579069225611 := by
  unfold tailWord_8371406
  simp only [CollatzResearch.WordTrace]
  refine ⟨38166282588729157395487759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203553507139888839442601381 38166282588729157395487759)
  ·
    refine ⟨57249423883093736093231639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38166282588729157395487759 57249423883093736093231639)
    ·
      refine ⟨85874135824640604139847459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57249423883093736093231639 85874135824640604139847459)
      ·
        refine ⟨128811203736960906209771189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85874135824640604139847459 128811203736960906209771189)
        ·
          refine ⟨12076050350340084957166049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128811203736960906209771189 12076050350340084957166049)
          ·
            refine ⟨9057037762755063717874537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12076050350340084957166049 9057037762755063717874537)
            ·
              refine ⟨6792778322066297788405903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9057037762755063717874537 6792778322066297788405903)
              ·
                refine ⟨10189167483099446682608855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792778322066297788405903 10189167483099446682608855)
                ·
                  refine ⟨15283751224649170023913283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10189167483099446682608855 15283751224649170023913283)
                  ·
                    refine ⟨22925626836973755035869925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15283751224649170023913283 22925626836973755035869925)
                    ·
                      refine ⟨4298555031932579069225611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22925626836973755035869925 4298555031932579069225611)
                      ·
                        rfl

theorem cell23_8371406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_8371406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371406 prefixEnd_8371406 := by exact prefixLift 8371406
  have htrace : WordTrace (prefixWord ++ tailWord_8371406) baseStart_8371406 baseEnd_8371406 := by
    simpa [prefixWord, tailWord_8371406, baseEnd_8371406] using wordTrace_append hprefix tailTrace_8371406
  have hstable : (prefixWord ++ tailWord_8371406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371406).length < 2 ^ (prefixWord ++ tailWord_8371406).sum := by decide
  have hdescent : baseEnd_8371406 < baseStart_8371406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371412 : List Nat := [2, 4, 1, 4, 1, 1, 10]
def baseStart_8371412 : Nat := 118140960795 + 8371412 * 2 ^ 59
def prefixEnd_8371412 : Nat := 4983230072969 + 3 ^ 40 * 8371412 * 2
def baseEnd_8371412 : Nat := 53068618676746988219143

theorem tailTrace_8371412 : CollatzResearch.WordTrace tailWord_8371412 prefixEnd_8371412 53068618676746988219143 := by
  unfold tailWord_8371412
  simp only [CollatzResearch.WordTrace]
  refine ⟨152665239773905761094310245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203553653031874348125746993 152665239773905761094310245)
  ·
    refine ⟨28624732457607330205183171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152665239773905761094310245 28624732457607330205183171)
    ·
      refine ⟨42937098686410995307774757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624732457607330205183171 42937098686410995307774757)
      ·
        refine ⟨8050706003702061620207767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42937098686410995307774757 8050706003702061620207767)
        ·
          refine ⟨12076059005553092430311651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050706003702061620207767 12076059005553092430311651)
          ·
            refine ⟨18114088508329638645467477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12076059005553092430311651 18114088508329638645467477)
            ·
              refine ⟨53068618676746988219143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18114088508329638645467477 53068618676746988219143)
              ·
                rfl

theorem cell23_8371412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 10].length) (baseStart_8371412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371412 prefixEnd_8371412 := by exact prefixLift 8371412
  have htrace : WordTrace (prefixWord ++ tailWord_8371412) baseStart_8371412 baseEnd_8371412 := by
    simpa [prefixWord, tailWord_8371412, baseEnd_8371412] using wordTrace_append hprefix tailTrace_8371412
  have hstable : (prefixWord ++ tailWord_8371412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371412).length < 2 ^ (prefixWord ++ tailWord_8371412).sum := by decide
  have hdescent : baseEnd_8371412 < baseStart_8371412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371416 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 2, 4]
def baseStart_8371416 : Nat := 118140960795 + 8371416 * 2 ^ 59
def prefixEnd_8371416 : Nat := 4983230072969 + 3 ^ 40 * 8371416 * 2
def baseEnd_8371416 : Nat := 1432853388913041343366855

theorem tailTrace_8371416 : CollatzResearch.WordTrace tailWord_8371416 prefixEnd_8371416 1432853388913041343366855 := by
  unfold tailWord_8371416
  simp only [CollatzResearch.WordTrace]
  refine ⟨152665312719898515435883051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203553750293198020581177401 152665312719898515435883051)
  ·
    refine ⟨228997969079847773153824577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152665312719898515435883051 228997969079847773153824577)
    ·
      refine ⟨171748476809885829865368433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228997969079847773153824577 171748476809885829865368433)
      ·
        refine ⟨128811357607414372399026325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171748476809885829865368433 128811357607414372399026325)
        ·
          refine ⟨6038032387847548706204359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128811357607414372399026325 6038032387847548706204359)
          ·
            refine ⟨9057048581771323059306539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038032387847548706204359 9057048581771323059306539)
            ·
              refine ⟨13585572872656984588959809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057048581771323059306539 13585572872656984588959809)
              ·
                refine ⟨10189179654492738441719857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13585572872656984588959809 10189179654492738441719857)
                ·
                  refine ⟨7641884740869553831289893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10189179654492738441719857 7641884740869553831289893)
                  ·
                    refine ⟨1432853388913041343366855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7641884740869553831289893 1432853388913041343366855)
                    ·
                      rfl

theorem cell23_8371416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_8371416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371416 prefixEnd_8371416 := by exact prefixLift 8371416
  have htrace : WordTrace (prefixWord ++ tailWord_8371416) baseStart_8371416 baseEnd_8371416 := by
    simpa [prefixWord, tailWord_8371416, baseEnd_8371416] using wordTrace_append hprefix tailTrace_8371416
  have hstable : (prefixWord ++ tailWord_8371416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371416).length < 2 ^ (prefixWord ++ tailWord_8371416).sum := by decide
  have hdescent : baseEnd_8371416 < baseStart_8371416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371439 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_8371439 : Nat := 118140960795 + 8371439 * 2 ^ 59
def prefixEnd_8371439 : Nat := 4983230072969 + 3 ^ 40 * 8371439 * 2
def baseEnd_8371439 : Nat := 4298571976794177440112959

theorem tailTrace_8371439 : CollatzResearch.WordTrace tailWord_8371439 prefixEnd_8371439 4298571976794177440112959 := by
  unfold tailWord_8371439
  simp only [CollatzResearch.WordTrace]
  refine ⟨305331464318713705799853371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203554309545809137199902247 305331464318713705799853371)
  ·
    refine ⟨457997196478070558699780057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305331464318713705799853371 457997196478070558699780057)
    ·
      refine ⟨343497897358552919024835043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457997196478070558699780057 343497897358552919024835043)
      ·
        refine ⟨515246846037829378537252565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343497897358552919024835043 515246846037829378537252565)
        ·
          refine ⟨12076097954011626059466857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 515246846037829378537252565 12076097954011626059466857)
          ·
            refine ⟨9057073465508719544600143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12076097954011626059466857 9057073465508719544600143)
            ·
              refine ⟨13585610198263079316900215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057073465508719544600143 13585610198263079316900215)
              ·
                refine ⟨20378415297394618975350323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13585610198263079316900215 20378415297394618975350323)
                ·
                  refine ⟨30567622946091928463025485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20378415297394618975350323 30567622946091928463025485)
                  ·
                    refine ⟨11462858604784473173634557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30567622946091928463025485 11462858604784473173634557)
                    ·
                      refine ⟨4298571976794177440112959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462858604784473173634557 4298571976794177440112959)
                      ·
                        rfl

theorem cell23_8371439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_8371439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371439 prefixEnd_8371439 := by exact prefixLift 8371439
  have htrace : WordTrace (prefixWord ++ tailWord_8371439) baseStart_8371439 baseEnd_8371439 := by
    simpa [prefixWord, tailWord_8371439, baseEnd_8371439] using wordTrace_append hprefix tailTrace_8371439
  have hstable : (prefixWord ++ tailWord_8371439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371439).length < 2 ^ (prefixWord ++ tailWord_8371439).sum := by decide
  have hdescent : baseEnd_8371439 < baseStart_8371439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371449 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 1, 3, 2]
def baseStart_8371449 : Nat := 118140960795 + 8371449 * 2 ^ 59
def prefixEnd_8371449 : Nat := 4983230072969 + 3 ^ 40 * 8371449 * 2
def baseEnd_8371449 : Nat := 4298577111600722400987913

theorem tailTrace_8371449 : CollatzResearch.WordTrace tailWord_8371449 prefixEnd_8371449 4298577111600722400987913 := by
  unfold tailWord_8371449
  simp only [CollatzResearch.WordTrace]
  refine ⟨305331829048677477507717401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203554552699118318338478267 305331829048677477507717401)
  ·
    refine ⟨228998871786508108130788051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305331829048677477507717401 228998871786508108130788051)
    ·
      refine ⟨343498307679762162196182077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228998871786508108130788051 343498307679762162196182077)
      ·
        refine ⟨128811865379910810823568279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343498307679762162196182077 128811865379910810823568279)
        ·
          refine ⟨193217798069866216235352419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128811865379910810823568279 193217798069866216235352419)
          ·
            refine ⟨289826697104799324353028629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193217798069866216235352419 289826697104799324353028629)
            ·
              refine ⟨13585626426787468329048217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289826697104799324353028629 13585626426787468329048217)
              ·
                refine ⟨10189219820090601246786163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13585626426787468329048217 10189219820090601246786163)
                ·
                  refine ⟨15283829730135901870179245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10189219820090601246786163 15283829730135901870179245)
                  ·
                    refine ⟨5731436148800963201317217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15283829730135901870179245 5731436148800963201317217)
                    ·
                      refine ⟨4298577111600722400987913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731436148800963201317217 4298577111600722400987913)
                      ·
                        rfl

theorem cell23_8371449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_8371449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371449 prefixEnd_8371449 := by exact prefixLift 8371449
  have htrace : WordTrace (prefixWord ++ tailWord_8371449) baseStart_8371449 baseEnd_8371449 := by
    simpa [prefixWord, tailWord_8371449, baseEnd_8371449] using wordTrace_append hprefix tailTrace_8371449
  have hstable : (prefixWord ++ tailWord_8371449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371449).length < 2 ^ (prefixWord ++ tailWord_8371449).sum := by decide
  have hdescent : baseEnd_8371449 < baseStart_8371449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371465 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_8371465 : Nat := 118140960795 + 8371465 * 2 ^ 59
def prefixEnd_8371465 : Nat := 4983230072969 + 3 ^ 40 * 8371465 * 2
def baseEnd_8371465 : Nat := 4298585327291194338387839

theorem tailTrace_8371465 : CollatzResearch.WordTrace tailWord_8371465 prefixEnd_8371465 4298585327291194338387839 := by
  unfold tailWord_8371465
  simp only [CollatzResearch.WordTrace]
  refine ⟨305332412616619512240299849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203554941744413008160199899 305332412616619512240299849)
  ·
    refine ⟨228999309462464634180224887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305332412616619512240299849 228999309462464634180224887)
    ·
      refine ⟨343498964193696951270337331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228999309462464634180224887 343498964193696951270337331)
      ·
        refine ⟨515248446290545426905505997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343498964193696951270337331 515248446290545426905505997)
        ·
          refine ⟨193218167358954535089564749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515248446290545426905505997 193218167358954535089564749)
          ·
            refine ⟨72456812759607950658586781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193218167358954535089564749 72456812759607950658586781)
            ·
              refine ⟨27171304784852981496970043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72456812759607950658586781 27171304784852981496970043)
              ·
                refine ⟨40756957177279472245455065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27171304784852981496970043 40756957177279472245455065)
                ·
                  refine ⟨30567717882959604184091299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40756957177279472245455065 30567717882959604184091299)
                  ·
                    refine ⟨45851576824439406276136949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30567717882959604184091299 45851576824439406276136949)
                    ·
                      refine ⟨4298585327291194338387839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45851576824439406276136949 4298585327291194338387839)
                      ·
                        rfl

theorem cell23_8371465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_8371465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371465 prefixEnd_8371465 := by exact prefixLift 8371465
  have htrace : WordTrace (prefixWord ++ tailWord_8371465) baseStart_8371465 baseEnd_8371465 := by
    simpa [prefixWord, tailWord_8371465, baseEnd_8371465] using wordTrace_append hprefix tailTrace_8371465
  have hstable : (prefixWord ++ tailWord_8371465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371465).length < 2 ^ (prefixWord ++ tailWord_8371465).sum := by decide
  have hdescent : baseEnd_8371465 < baseStart_8371465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371479 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_8371479 : Nat := 118140960795 + 8371479 * 2 ^ 59
def prefixEnd_8371479 : Nat := 4983230072969 + 3 ^ 40 * 8371479 * 2
def baseEnd_8371479 : Nat := 4298592516020357283612775

theorem tailTrace_8371479 : CollatzResearch.WordTrace tailWord_8371479 prefixEnd_8371479 4298592516020357283612775 := by
  unfold tailWord_8371479
  simp only [CollatzResearch.WordTrace]
  refine ⟨305332923238568792631309491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203555282159045861754206327 305332923238568792631309491)
  ·
    refine ⟨457999384857853188946964237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305332923238568792631309491 457999384857853188946964237)
    ·
      refine ⟨171749769321694945855111589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457999384857853188946964237 171749769321694945855111589)
      ·
        refine ⟨32203081747817802347833423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171749769321694945855111589 32203081747817802347833423)
        ·
          refine ⟨48304622621726703521750135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32203081747817802347833423 48304622621726703521750135)
          ·
            refine ⟨72456933932590055282625203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48304622621726703521750135 72456933932590055282625203)
            ·
              refine ⟨108685400898885082923937805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72456933932590055282625203 108685400898885082923937805)
              ·
                refine ⟨40757025337081906096476677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108685400898885082923937805 40757025337081906096476677)
                ·
                  refine ⟨7641942250702857393089377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40757025337081906096476677 7641942250702857393089377)
                  ·
                    refine ⟨5731456688027143044817033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7641942250702857393089377 5731456688027143044817033)
                    ·
                      refine ⟨4298592516020357283612775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731456688027143044817033 4298592516020357283612775)
                      ·
                        rfl

theorem cell23_8371479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_8371479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371479 prefixEnd_8371479 := by exact prefixLift 8371479
  have htrace : WordTrace (prefixWord ++ tailWord_8371479) baseStart_8371479 baseEnd_8371479 := by
    simpa [prefixWord, tailWord_8371479, baseEnd_8371479] using wordTrace_append hprefix tailTrace_8371479
  have hstable : (prefixWord ++ tailWord_8371479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371479).length < 2 ^ (prefixWord ++ tailWord_8371479).sum := by decide
  have hdescent : baseEnd_8371479 < baseStart_8371479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371490 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_8371490 : Nat := 118140960795 + 8371490 * 2 ^ 59
def prefixEnd_8371490 : Nat := 4983230072969 + 3 ^ 40 * 8371490 * 2
def baseEnd_8371490 : Nat := 4298598164307556740575225

theorem tailTrace_8371490 : CollatzResearch.WordTrace tailWord_8371490 prefixEnd_8371490 4298598164307556740575225 := by
  unfold tailWord_8371490
  simp only [CollatzResearch.WordTrace]
  refine ⟨76333331110382235377489981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203555549627685961006639949 76333331110382235377489981)
  ·
    refine ⟨28624999166393338266558743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76333331110382235377489981 28624999166393338266558743)
    ·
      refine ⟨42937498749590007399838115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624999166393338266558743 42937498749590007399838115)
      ·
        refine ⟨64406248124385011099757173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42937498749590007399838115 64406248124385011099757173)
        ·
          refine ⟨6038085761661094790602235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64406248124385011099757173 6038085761661094790602235)
          ·
            refine ⟨9057128642491642185903353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038085761661094790602235 9057128642491642185903353)
            ·
              refine ⟨6792846481868731639427515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9057128642491642185903353 6792846481868731639427515)
              ·
                refine ⟨10189269722803097459141273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792846481868731639427515 10189269722803097459141273)
                ·
                  refine ⟨7641952292102323094355955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10189269722803097459141273 7641952292102323094355955)
                  ·
                    refine ⟨11462928438153484641533933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7641952292102323094355955 11462928438153484641533933)
                    ·
                      refine ⟨4298598164307556740575225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11462928438153484641533933 4298598164307556740575225)
                      ·
                        rfl

theorem cell23_8371490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_8371490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371490 prefixEnd_8371490 := by exact prefixLift 8371490
  have htrace : WordTrace (prefixWord ++ tailWord_8371490) baseStart_8371490 baseEnd_8371490 := by
    simpa [prefixWord, tailWord_8371490, baseEnd_8371490] using wordTrace_append hprefix tailTrace_8371490
  have hstable : (prefixWord ++ tailWord_8371490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371490).length < 2 ^ (prefixWord ++ tailWord_8371490).sum := by decide
  have hdescent : baseEnd_8371490 < baseStart_8371490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371532 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_8371532 : Nat := 118140960795 + 8371532 * 2 ^ 59
def prefixEnd_8371532 : Nat := 4983230072969 + 3 ^ 40 * 8371532 * 2
def baseEnd_8371532 : Nat := 1432873243498348525416677

theorem tailTrace_8371532 : CollatzResearch.WordTrace tailWord_8371532 prefixEnd_8371532 1432873243498348525416677 := by
  unfold tailWord_8371532
  simp only [CollatzResearch.WordTrace]
  refine ⟨152667428153688391341494425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203556570871584521788659233 152667428153688391341494425)
  ·
    refine ⟨114500571115266293506120819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152667428153688391341494425 114500571115266293506120819)
    ·
      refine ⟨171750856672899440259181229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114500571115266293506120819 171750856672899440259181229)
      ·
        refine ⟨64406571252337290097192961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171750856672899440259181229 64406571252337290097192961)
        ·
          refine ⟨48304928439252967572894721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64406571252337290097192961 48304928439252967572894721)
          ·
            refine ⟨36228696329439725679671041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48304928439252967572894721 36228696329439725679671041)
            ·
              refine ⟨27171522247079794259753281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36228696329439725679671041 27171522247079794259753281)
              ·
                refine ⟨20378641685309845694814961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27171522247079794259753281 20378641685309845694814961)
                ·
                  refine ⟨15283981263982384271111221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20378641685309845694814961 15283981263982384271111221)
                  ·
                    refine ⟨1432873243498348525416677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15283981263982384271111221 1432873243498348525416677)
                    ·
                      rfl

theorem cell23_8371532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_8371532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371532 prefixEnd_8371532 := by exact prefixLift 8371532
  have htrace : WordTrace (prefixWord ++ tailWord_8371532) baseStart_8371532 baseEnd_8371532 := by
    simpa [prefixWord, tailWord_8371532, baseEnd_8371532] using wordTrace_append hprefix tailTrace_8371532
  have hstable : (prefixWord ++ tailWord_8371532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371532).length < 2 ^ (prefixWord ++ tailWord_8371532).sum := by decide
  have hdescent : baseEnd_8371532 < baseStart_8371532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371575 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 8]
def baseStart_8371575 : Nat := 118140960795 + 8371575 * 2 ^ 59
def prefixEnd_8371575 : Nat := 4983230072969 + 3 ^ 40 * 8371575 * 2
def baseEnd_8371575 : Nat := 477626867795909878668037

theorem tailTrace_8371575 : CollatzResearch.WordTrace tailWord_8371575 prefixEnd_8371575 477626867795909878668037 := by
  unfold tailWord_8371575
  simp only [CollatzResearch.WordTrace]
  refine ⟨305336424646221001026804179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203557616430814000684536119 305336424646221001026804179)
  ·
    refine ⟨458004636969331501540206269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305336424646221001026804179 458004636969331501540206269)
    ·
      refine ⟨171751738863499313077577351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458004636969331501540206269 171751738863499313077577351)
      ·
        refine ⟨257627608295248969616366027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171751738863499313077577351 257627608295248969616366027)
        ·
          refine ⟨386441412442873454424549041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257627608295248969616366027 386441412442873454424549041)
          ·
            refine ⟨289831059332155090818411781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386441412442873454424549041 289831059332155090818411781)
            ·
              refine ⟨54343323624779079528452209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289831059332155090818411781 54343323624779079528452209)
              ·
                refine ⟨40757492718584309646339157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54343323624779079528452209 40757492718584309646339157)
                ·
                  refine ⟨477626867795909878668037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40757492718584309646339157 477626867795909878668037)
                  ·
                    rfl

theorem cell23_8371575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 8].length) (baseStart_8371575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371575 prefixEnd_8371575 := by exact prefixLift 8371575
  have htrace : WordTrace (prefixWord ++ tailWord_8371575) baseStart_8371575 baseEnd_8371575 := by
    simpa [prefixWord, tailWord_8371575, baseEnd_8371575] using wordTrace_append hprefix tailTrace_8371575
  have hstable : (prefixWord ++ tailWord_8371575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371575).length < 2 ^ (prefixWord ++ tailWord_8371575).sum := by decide
  have hdescent : baseEnd_8371575 < baseStart_8371575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371592 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 8]
def baseStart_8371592 : Nat := 118140960795 + 8371592 * 2 ^ 59
def prefixEnd_8371592 : Nat := 4983230072969 + 3 ^ 40 * 8371592 * 2
def baseEnd_8371592 : Nat := 477627837703812815722195

theorem tailTrace_8371592 : CollatzResearch.WordTrace tailWord_8371592 prefixEnd_8371592 477627837703812815722195 := by
  unfold tailWord_8371592
  simp only [CollatzResearch.WordTrace]
  refine ⟨152668522343579706465086515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203558029791439608620115353 152668522343579706465086515)
  ·
    refine ⟨229002783515369559697629773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152668522343579706465086515 229002783515369559697629773)
    ·
      refine ⟨85876043818263584886611165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229002783515369559697629773 85876043818263584886611165)
      ·
        refine ⟨32203516431848844332479187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85876043818263584886611165 32203516431848844332479187)
        ·
          refine ⟨48305274647773266498718781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32203516431848844332479187 48305274647773266498718781)
          ·
            refine ⟨18114477992914974937019543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48305274647773266498718781 18114477992914974937019543)
            ·
              refine ⟨27171716989372462405529315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18114477992914974937019543 27171716989372462405529315)
              ·
                refine ⟨40757575484058693608293973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27171716989372462405529315 40757575484058693608293973)
                ·
                  refine ⟨477627837703812815722195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40757575484058693608293973 477627837703812815722195)
                  ·
                    rfl

theorem cell23_8371592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_8371592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371592 prefixEnd_8371592 := by exact prefixLift 8371592
  have htrace : WordTrace (prefixWord ++ tailWord_8371592) baseStart_8371592 baseEnd_8371592 := by
    simpa [prefixWord, tailWord_8371592, baseEnd_8371592] using wordTrace_append hprefix tailTrace_8371592
  have hstable : (prefixWord ++ tailWord_8371592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371592).length < 2 ^ (prefixWord ++ tailWord_8371592).sum := by decide
  have hdescent : baseEnd_8371592 < baseStart_8371592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371595 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_8371595 : Nat := 118140960795 + 8371595 * 2 ^ 59
def prefixEnd_8371595 : Nat := 4983230072969 + 3 ^ 40 * 8371595 * 2
def baseEnd_8371595 : Nat := 4298652079776278829762241

theorem tailTrace_8371595 : CollatzResearch.WordTrace tailWord_8371595 prefixEnd_8371595 4298652079776278829762241 := by
  unfold tailWord_8371595
  simp only [CollatzResearch.WordTrace]
  refine ⟨305337154106148544442532239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203558102737432362961688159 305337154106148544442532239)
  ·
    refine ⟨458005731159222816663798359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305337154106148544442532239 458005731159222816663798359)
    ·
      refine ⟨687008596738834224995697539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458005731159222816663798359 687008596738834224995697539)
      ·
        refine ⟨1030512895108251337493546309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687008596738834224995697539 1030512895108251337493546309)
        ·
          refine ⟨193221167832797125780039933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1030512895108251337493546309 193221167832797125780039933)
          ·
            refine ⟨72457937937298922167514975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193221167832797125780039933 72457937937298922167514975)
            ·
              refine ⟨108686906905948383251272463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72457937937298922167514975 108686906905948383251272463)
              ·
                refine ⟨163030360358922574876908695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108686906905948383251272463 163030360358922574876908695)
                ·
                  refine ⟨244545540538383862315363043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163030360358922574876908695 244545540538383862315363043)
                  ·
                    refine ⟨366818310807575793473044565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244545540538383862315363043 366818310807575793473044565)
                    ·
                      refine ⟨4298652079776278829762241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 366818310807575793473044565 4298652079776278829762241)
                      ·
                        rfl

theorem cell23_8371595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_8371595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371595 prefixEnd_8371595 := by exact prefixLift 8371595
  have htrace : WordTrace (prefixWord ++ tailWord_8371595) baseStart_8371595 baseEnd_8371595 := by
    simpa [prefixWord, tailWord_8371595, baseEnd_8371595] using wordTrace_append hprefix tailTrace_8371595
  have hstable : (prefixWord ++ tailWord_8371595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371595).length < 2 ^ (prefixWord ++ tailWord_8371595).sum := by decide
  have hdescent : baseEnd_8371595 < baseStart_8371595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371609 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 6]
def baseStart_8371609 : Nat := 118140960795 + 8371609 * 2 ^ 59
def prefixEnd_8371609 : Nat := 4983230072969 + 3 ^ 40 * 8371609 * 2
def baseEnd_8371609 : Nat := 477628807611715752776353

theorem tailTrace_8371609 : CollatzResearch.WordTrace tailWord_8371609 prefixEnd_8371609 477628807611715752776353 := by
  unfold tailWord_8371609
  simp only [CollatzResearch.WordTrace]
  refine ⟨305337664728097824833541881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203558443152065216555694587 305337664728097824833541881)
  ·
    refine ⟨229003248546073368625156411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305337664728097824833541881 229003248546073368625156411)
    ·
      refine ⟨343504872819110052937734617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229003248546073368625156411 343504872819110052937734617)
      ·
        refine ⟨257628654614332539703300963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343504872819110052937734617 257628654614332539703300963)
        ·
          refine ⟨386442981921498809554951445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257628654614332539703300963 386442981921498809554951445)
          ·
            refine ⟨18114514777570256697888349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 386442981921498809554951445 18114514777570256697888349)
            ·
              refine ⟨6792943041588846261708131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18114514777570256697888349 6792943041588846261708131)
              ·
                refine ⟨10189414562383269392562197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792943041588846261708131 10189414562383269392562197)
                ·
                  refine ⟨477628807611715752776353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10189414562383269392562197 477628807611715752776353)
                  ·
                    rfl

theorem cell23_8371609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 6].length) (baseStart_8371609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371609 prefixEnd_8371609 := by exact prefixLift 8371609
  have htrace : WordTrace (prefixWord ++ tailWord_8371609) baseStart_8371609 baseEnd_8371609 := by
    simpa [prefixWord, tailWord_8371609, baseEnd_8371609] using wordTrace_append hprefix tailTrace_8371609
  have hstable : (prefixWord ++ tailWord_8371609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371609).length < 2 ^ (prefixWord ++ tailWord_8371609).sum := by decide
  have hdescent : baseEnd_8371609 < baseStart_8371609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371619 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 3]
def baseStart_8371619 : Nat := 118140960795 + 8371619 * 2 ^ 59
def prefixEnd_8371619 : Nat := 4983230072969 + 3 ^ 40 * 8371619 * 2
def baseEnd_8371619 : Nat := 4298664403311986735862131

theorem tailTrace_8371619 : CollatzResearch.WordTrace tailWord_8371619 prefixEnd_8371619 4298664403311986735862131 := by
  unfold tailWord_8371619
  simp only [CollatzResearch.WordTrace]
  refine ⟨305338029458061596541405911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203558686305374397694270607 305338029458061596541405911)
  ·
    refine ⟨458007044187092394812108867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305338029458061596541405911 458007044187092394812108867)
    ·
      refine ⟨687010566280638592218163301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458007044187092394812108867 687010566280638592218163301)
      ·
        refine ⟨128814481177619736040905619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687010566280638592218163301 128814481177619736040905619)
        ·
          refine ⟨193221721766429604061358429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128814481177619736040905619 193221721766429604061358429)
          ·
            refine ⟨72458145662411101523009411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193221721766429604061358429 72458145662411101523009411)
            ·
              refine ⟨108687218493616652284514117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72458145662411101523009411 108687218493616652284514117)
              ·
                refine ⟨20378853467553122303346397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108687218493616652284514117 20378853467553122303346397)
                ·
                  refine ⟨7642070050332420863754899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20378853467553122303346397 7642070050332420863754899)
                  ·
                    refine ⟨11463105075498631295632349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7642070050332420863754899 11463105075498631295632349)
                    ·
                      refine ⟨4298664403311986735862131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11463105075498631295632349 4298664403311986735862131)
                      ·
                        rfl

theorem cell23_8371619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_8371619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371619 prefixEnd_8371619 := by exact prefixLift 8371619
  have htrace : WordTrace (prefixWord ++ tailWord_8371619) baseStart_8371619 baseEnd_8371619 := by
    simpa [prefixWord, tailWord_8371619, baseEnd_8371619] using wordTrace_append hprefix tailTrace_8371619
  have hstable : (prefixWord ++ tailWord_8371619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371619).length < 2 ^ (prefixWord ++ tailWord_8371619).sum := by decide
  have hdescent : baseEnd_8371619 < baseStart_8371619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371642 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_8371642 : Nat := 118140960795 + 8371642 * 2 ^ 59
def prefixEnd_8371642 : Nat := 4983230072969 + 3 ^ 40 * 8371642 * 2
def baseEnd_8371642 : Nat := 4298676213367040145874525

theorem tailTrace_8371642 : CollatzResearch.WordTrace tailWord_8371642 prefixEnd_8371642 4298676213367040145874525 := by
  unfold tailWord_8371642
  simp only [CollatzResearch.WordTrace]
  refine ⟨76334717084244567867373295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203559245557985514312995453 76334717084244567867373295)
  ·
    refine ⟨114502075626366851801059943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76334717084244567867373295 114502075626366851801059943)
    ·
      refine ⟨171753113439550277701589915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114502075626366851801059943 171753113439550277701589915)
      ·
        refine ⟨257629670159325416552384873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171753113439550277701589915 257629670159325416552384873)
        ·
          refine ⟨193222252619494062414288655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257629670159325416552384873 193222252619494062414288655)
          ·
            refine ⟨289833378929241093621432983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193222252619494062414288655 289833378929241093621432983)
            ·
              refine ⟨434750068393861640432149475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289833378929241093621432983 434750068393861640432149475)
              ·
                refine ⟨652125102590792460648224213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434750068393861640432149475 652125102590792460648224213)
                ·
                  refine ⟨15284182091971698296442755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 652125102590792460648224213 15284182091971698296442755)
                  ·
                    refine ⟨22926273137957547444664133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15284182091971698296442755 22926273137957547444664133)
                    ·
                      refine ⟨4298676213367040145874525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22926273137957547444664133 4298676213367040145874525)
                      ·
                        rfl

theorem cell23_8371642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_8371642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371642 prefixEnd_8371642 := by exact prefixLift 8371642
  have htrace : WordTrace (prefixWord ++ tailWord_8371642) baseStart_8371642 baseEnd_8371642 := by
    simpa [prefixWord, tailWord_8371642, baseEnd_8371642] using wordTrace_append hprefix tailTrace_8371642
  have hstable : (prefixWord ++ tailWord_8371642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371642).length < 2 ^ (prefixWord ++ tailWord_8371642).sum := by decide
  have hdescent : baseEnd_8371642 < baseStart_8371642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371672 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_8371672 : Nat := 118140960795 + 8371672 * 2 ^ 59
def prefixEnd_8371672 : Nat := 4983230072969 + 3 ^ 40 * 8371672 * 2
def baseEnd_8371672 : Nat := 4298691617786675028499387

theorem tailTrace_8371672 : CollatzResearch.WordTrace tailWord_8371672 prefixEnd_8371672 4298691617786675028499387 := by
  unfold tailWord_8371672
  simp only [CollatzResearch.WordTrace]
  refine ⟨152669981263434793296542635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203559975017913057728723513 152669981263434793296542635)
  ·
    refine ⟨229004971895152189944813953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152669981263434793296542635 229004971895152189944813953)
    ·
      refine ⟨171753728921364142458610465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229004971895152189944813953 171753728921364142458610465)
      ·
        refine ⟨128815296691023106843957849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171753728921364142458610465 128815296691023106843957849)
        ·
          refine ⟨96611472518267330132968387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128815296691023106843957849 96611472518267330132968387)
          ·
            refine ⟨144917208777400995199452581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96611472518267330132968387 144917208777400995199452581)
            ·
              refine ⟨27171976645762686599897359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144917208777400995199452581 27171976645762686599897359)
              ·
                refine ⟨40757964968644029899846039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27171976645762686599897359 40757964968644029899846039)
                ·
                  refine ⟨61136947452966044849769059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40757964968644029899846039 61136947452966044849769059)
                  ·
                    refine ⟨91705421179449067274653589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61136947452966044849769059 91705421179449067274653589)
                    ·
                      refine ⟨4298691617786675028499387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91705421179449067274653589 4298691617786675028499387)
                      ·
                        rfl

theorem cell23_8371672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_8371672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371672 prefixEnd_8371672 := by exact prefixLift 8371672
  have htrace : WordTrace (prefixWord ++ tailWord_8371672) baseStart_8371672 baseEnd_8371672 := by
    simpa [prefixWord, tailWord_8371672, baseEnd_8371672] using wordTrace_append hprefix tailTrace_8371672
  have hstable : (prefixWord ++ tailWord_8371672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371672).length < 2 ^ (prefixWord ++ tailWord_8371672).sum := by decide
  have hdescent : baseEnd_8371672 < baseStart_8371672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371679 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_8371679 : Nat := 118140960795 + 8371679 * 2 ^ 59
def prefixEnd_8371679 : Nat := 4983230072969 + 3 ^ 40 * 8371679 * 2
def baseEnd_8371679 : Nat := 4298695212151256501111855

theorem tailTrace_8371679 : CollatzResearch.WordTrace tailWord_8371679 prefixEnd_8371679 4298695212151256501111855 := by
  unfold tailWord_8371679
  simp only [CollatzResearch.WordTrace]
  refine ⟨305340217837844226788590091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203560145225229484525726727 305340217837844226788590091)
  ·
    refine ⟨458010326756766340182885137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305340217837844226788590091 458010326756766340182885137)
    ·
      refine ⟨343507745067574755137163853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458010326756766340182885137 343507745067574755137163853)
      ·
        refine ⟨128815404400340533176436445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343507745067574755137163853 128815404400340533176436445)
        ·
          refine ⟨48305776650127699941163667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128815404400340533176436445 48305776650127699941163667)
          ·
            refine ⟨72458664975191549911745501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48305776650127699941163667 72458664975191549911745501)
            ·
              refine ⟨27171999365696831216904563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72458664975191549911745501 27171999365696831216904563)
              ·
                refine ⟨40757999048545246825356845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27171999365696831216904563 40757999048545246825356845)
                ·
                  refine ⟨15284249643204467559508817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40757999048545246825356845 15284249643204467559508817)
                  ·
                    refine ⟨11463187232403350669631613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15284249643204467559508817 11463187232403350669631613)
                    ·
                      refine ⟨4298695212151256501111855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11463187232403350669631613 4298695212151256501111855)
                      ·
                        rfl

theorem cell23_8371679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_8371679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371679 prefixEnd_8371679 := by exact prefixLift 8371679
  have htrace : WordTrace (prefixWord ++ tailWord_8371679) baseStart_8371679 baseEnd_8371679 := by
    simpa [prefixWord, tailWord_8371679, baseEnd_8371679] using wordTrace_append hprefix tailTrace_8371679
  have hstable : (prefixWord ++ tailWord_8371679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371679).length < 2 ^ (prefixWord ++ tailWord_8371679).sum := by decide
  have hdescent : baseEnd_8371679 < baseStart_8371679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371716 : List Nat := [2, 3, 2, 3, 2, 2, 1, 8]
def baseStart_8371716 : Nat := 118140960795 + 8371716 * 2 ^ 59
def prefixEnd_8371716 : Nat := 4983230072969 + 3 ^ 40 * 8371716 * 2
def baseEnd_8371716 : Nat := 159211637442054550235155

theorem tailTrace_8371716 : CollatzResearch.WordTrace tailWord_8371716 prefixEnd_8371716 159211637442054550235155 := by
  unfold tailWord_8371716
  simp only [CollatzResearch.WordTrace]
  refine ⟨152670783669355091053843501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203561044892473454738458001 152670783669355091053843501)
  ·
    refine ⟨57251543876008159145191313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152670783669355091053843501 57251543876008159145191313)
    ·
      refine ⟨42938657907006119358893485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57251543876008159145191313 42938657907006119358893485)
      ·
        refine ⟨16101996715127294759585057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42938657907006119358893485 16101996715127294759585057)
        ·
          refine ⟨12076497536345471069688793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16101996715127294759585057 12076497536345471069688793)
          ·
            refine ⟨9057373152259103302266595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12076497536345471069688793 9057373152259103302266595)
            ·
              refine ⟨13586059728388654953399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057373152259103302266595 13586059728388654953399893)
              ·
                refine ⟨159211637442054550235155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13586059728388654953399893 159211637442054550235155)
                ·
                  rfl

theorem cell23_8371716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 8].length) (baseStart_8371716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371716 prefixEnd_8371716 := by exact prefixLift 8371716
  have htrace : WordTrace (prefixWord ++ tailWord_8371716) baseStart_8371716 baseEnd_8371716 := by
    simpa [prefixWord, tailWord_8371716, baseEnd_8371716] using wordTrace_append hprefix tailTrace_8371716
  have hstable : (prefixWord ++ tailWord_8371716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371716).length < 2 ^ (prefixWord ++ tailWord_8371716).sum := by decide
  have hdescent : baseEnd_8371716 < baseStart_8371716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371869 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_8371869 : Nat := 118140960795 + 8371869 * 2 ^ 59
def prefixEnd_8371869 : Nat := 4983230072969 + 3 ^ 40 * 8371869 * 2
def baseEnd_8371869 : Nat := 4298792773475610757735981

theorem tailTrace_8371869 : CollatzResearch.WordTrace tailWord_8371869 prefixEnd_8371869 4298792773475610757735981 := by
  unfold tailWord_8371869
  simp only [CollatzResearch.WordTrace]
  refine ⟨305347147707155889238006661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203564765138103926158671107 305347147707155889238006661)
  ·
    refine ⟨57252590195091729232126249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305347147707155889238006661 57252590195091729232126249)
    ·
      refine ⟨42939442646318796924094687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57252590195091729232126249 42939442646318796924094687)
      ·
        refine ⟨64409163969478195386142031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42939442646318796924094687 64409163969478195386142031)
        ·
          refine ⟨96613745954217293079213047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64409163969478195386142031 96613745954217293079213047)
          ·
            refine ⟨144920618931325939618819571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96613745954217293079213047 144920618931325939618819571)
            ·
              refine ⟨217380928396988909428229357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144920618931325939618819571 217380928396988909428229357)
              ·
                refine ⟨81517848148870841035586009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217380928396988909428229357 81517848148870841035586009)
                ·
                  refine ⟨61138386111653130776689507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81517848148870841035586009 61138386111653130776689507)
                  ·
                    refine ⟨91707579167479696165034261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61138386111653130776689507 91707579167479696165034261)
                    ·
                      refine ⟨4298792773475610757735981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91707579167479696165034261 4298792773475610757735981)
                      ·
                        rfl

theorem cell23_8371869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_8371869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371869 prefixEnd_8371869 := by exact prefixLift 8371869
  have htrace : WordTrace (prefixWord ++ tailWord_8371869) baseStart_8371869 baseEnd_8371869 := by
    simpa [prefixWord, tailWord_8371869, baseEnd_8371869] using wordTrace_append hprefix tailTrace_8371869
  have hstable : (prefixWord ++ tailWord_8371869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371869).length < 2 ^ (prefixWord ++ tailWord_8371869).sum := by decide
  have hdescent : baseEnd_8371869 < baseStart_8371869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371874 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_8371874 : Nat := 118140960795 + 8371874 * 2 ^ 59
def prefixEnd_8371874 : Nat := 4983230072969 + 3 ^ 40 * 8371874 * 2
def baseEnd_8371874 : Nat := 477643926764320359797051

theorem tailTrace_8371874 : CollatzResearch.WordTrace tailWord_8371874 prefixEnd_8371874 477643926764320359797051 := by
  unfold tailWord_8371874
  simp only [CollatzResearch.WordTrace]
  refine ⟨76336832518034443772984669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203564886714758516727959117 76336832518034443772984669)
  ·
    refine ⟨28626312194262916414869251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76336832518034443772984669 28626312194262916414869251)
    ·
      refine ⟨42939468291394374622303877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28626312194262916414869251 42939468291394374622303877)
      ·
        refine ⟨8051150304636445241681977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42939468291394374622303877 8051150304636445241681977)
        ·
          refine ⟨6038362728477333931261483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8051150304636445241681977 6038362728477333931261483)
          ·
            refine ⟨9057544092716000896892225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038362728477333931261483 9057544092716000896892225)
            ·
              refine ⟨6793158069537000672669169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9057544092716000896892225 6793158069537000672669169)
              ·
                refine ⟨5094868552152750504501877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793158069537000672669169 5094868552152750504501877)
                ·
                  refine ⟨477643926764320359797051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5094868552152750504501877 477643926764320359797051)
                  ·
                    rfl

theorem cell23_8371874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_8371874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371874 prefixEnd_8371874 := by exact prefixLift 8371874
  have htrace : WordTrace (prefixWord ++ tailWord_8371874) baseStart_8371874 baseEnd_8371874 := by
    simpa [prefixWord, tailWord_8371874, baseEnd_8371874] using wordTrace_append hprefix tailTrace_8371874
  have hstable : (prefixWord ++ tailWord_8371874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371874).length < 2 ^ (prefixWord ++ tailWord_8371874).sum := by decide
  have hdescent : baseEnd_8371874 < baseStart_8371874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371917 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_8371917 : Nat := 118140960795 + 8371917 * 2 ^ 59
def prefixEnd_8371917 : Nat := 4983230072969 + 3 ^ 40 * 8371917 * 2
def baseEnd_8371917 : Nat := 1432939140182342189978587

theorem tailTrace_8371917 : CollatzResearch.WordTrace tailWord_8371917 prefixEnd_8371917 1432939140182342189978587 := by
  unfold tailWord_8371917
  simp only [CollatzResearch.WordTrace]
  refine ⟨305348898410981993435754005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203565932273987995623836003 305348898410981993435754005)
  ·
    refine ⟨14313229613014780942300969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305348898410981993435754005 14313229613014780942300969)
    ·
      refine ⟨10734922209761085706725727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14313229613014780942300969 10734922209761085706725727)
      ·
        refine ⟨16102383314641628560088591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10734922209761085706725727 16102383314641628560088591)
        ·
          refine ⟨24153574971962442840132887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102383314641628560088591 24153574971962442840132887)
          ·
            refine ⟨36230362457943664260199331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24153574971962442840132887 36230362457943664260199331)
            ·
              refine ⟨54345543686915496390298997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36230362457943664260199331 54345543686915496390298997)
              ·
                refine ⟨5094894720648327786590531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54345543686915496390298997 5094894720648327786590531)
                ·
                  refine ⟨7642342080972491679885797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094894720648327786590531 7642342080972491679885797)
                  ·
                    refine ⟨1432939140182342189978587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7642342080972491679885797 1432939140182342189978587)
                    ·
                      rfl

theorem cell23_8371917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_8371917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371917 prefixEnd_8371917 := by exact prefixLift 8371917
  have htrace : WordTrace (prefixWord ++ tailWord_8371917) baseStart_8371917 baseEnd_8371917 := by
    simpa [prefixWord, tailWord_8371917, baseEnd_8371917] using wordTrace_append hprefix tailTrace_8371917
  have hstable : (prefixWord ++ tailWord_8371917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371917).length < 2 ^ (prefixWord ++ tailWord_8371917).sum := by decide
  have hdescent : baseEnd_8371917 < baseStart_8371917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371940 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_8371940 : Nat := 118140960795 + 8371940 * 2 ^ 59
def prefixEnd_8371940 : Nat := 4983230072969 + 3 ^ 40 * 8371940 * 2
def baseEnd_8371940 : Nat := 4298829230602079979948155

theorem tailTrace_8371940 : CollatzResearch.WordTrace tailWord_8371940 prefixEnd_8371940 4298829230602079979948155 := by
  unfold tailWord_8371940
  simp only [CollatzResearch.WordTrace]
  refine ⟨152674868644949334181920637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203566491526599112242560849 152674868644949334181920637)
  ·
    refine ⟨57253075741856000318220239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152674868644949334181920637 57253075741856000318220239)
    ·
      refine ⟨85879613612784000477330359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57253075741856000318220239 85879613612784000477330359)
      ·
        refine ⟨128819420419176000715995539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85879613612784000477330359 128819420419176000715995539)
        ·
          refine ⟨193229130628764001073993309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128819420419176000715995539 193229130628764001073993309)
          ·
            refine ⟨72460923985786500402747491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193229130628764001073993309 72460923985786500402747491)
            ·
              refine ⟨108691385978679750604121237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72460923985786500402747491 108691385978679750604121237)
              ·
                refine ⟨5094908717750613309568183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108691385978679750604121237 5094908717750613309568183)
                ·
                  refine ⟨7642363076625919964352275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094908717750613309568183 7642363076625919964352275)
                  ·
                    refine ⟨11463544614938879946528413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7642363076625919964352275 11463544614938879946528413)
                    ·
                      refine ⟨4298829230602079979948155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11463544614938879946528413 4298829230602079979948155)
                      ·
                        rfl

theorem cell23_8371940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_8371940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371940 prefixEnd_8371940 := by exact prefixLift 8371940
  have htrace : WordTrace (prefixWord ++ tailWord_8371940) baseStart_8371940 baseEnd_8371940 := by
    simpa [prefixWord, tailWord_8371940, baseEnd_8371940] using wordTrace_append hprefix tailTrace_8371940
  have hstable : (prefixWord ++ tailWord_8371940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371940).length < 2 ^ (prefixWord ++ tailWord_8371940).sum := by decide
  have hdescent : baseEnd_8371940 < baseStart_8371940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371946 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_8371946 : Nat := 118140960795 + 8371946 * 2 ^ 59
def prefixEnd_8371946 : Nat := 4983230072969 + 3 ^ 40 * 8371946 * 2
def baseEnd_8371946 : Nat := 4298832311486006956473127

theorem tailTrace_8371946 : CollatzResearch.WordTrace tailWord_8371946 prefixEnd_8371946 4298832311486006956473127 := by
  unfold tailWord_8371946
  simp only [CollatzResearch.WordTrace]
  refine ⟨76337489031969232847139923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203566637418584620925706461 76337489031969232847139923)
  ·
    refine ⟨114506233547953849270709885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76337489031969232847139923 114506233547953849270709885)
    ·
      refine ⟨42939837580482693476516207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114506233547953849270709885 42939837580482693476516207)
      ·
        refine ⟨64409756370724040214774311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42939837580482693476516207 64409756370724040214774311)
        ·
          refine ⟨96614634556086060322161467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64409756370724040214774311 96614634556086060322161467)
          ·
            refine ⟨144921951834129090483242201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96614634556086060322161467 144921951834129090483242201)
            ·
              refine ⟨108691463875596817862431651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144921951834129090483242201 108691463875596817862431651)
              ·
                refine ⟨163037195813395226793647477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108691463875596817862431651 163037195813395226793647477)
                ·
                  refine ⟨15284737107505802511904451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163037195813395226793647477 15284737107505802511904451)
                  ·
                    refine ⟨22927105661258703767856677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15284737107505802511904451 22927105661258703767856677)
                    ·
                      refine ⟨4298832311486006956473127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22927105661258703767856677 4298832311486006956473127)
                      ·
                        rfl

theorem cell23_8371946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_8371946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371946 prefixEnd_8371946 := by exact prefixLift 8371946
  have htrace : WordTrace (prefixWord ++ tailWord_8371946) baseStart_8371946 baseEnd_8371946 := by
    simpa [prefixWord, tailWord_8371946, baseEnd_8371946] using wordTrace_append hprefix tailTrace_8371946
  have hstable : (prefixWord ++ tailWord_8371946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371946).length < 2 ^ (prefixWord ++ tailWord_8371946).sum := by decide
  have hdescent : baseEnd_8371946 < baseStart_8371946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 5, 2, 2]
def baseStart_8371963 : Nat := 118140960795 + 8371963 * 2 ^ 59
def prefixEnd_8371963 : Nat := 4983230072969 + 3 ^ 40 * 8371963 * 2
def baseEnd_8371963 : Nat := 4298841040657133389960549

theorem tailTrace_8371963 : CollatzResearch.WordTrace tailWord_8371963 prefixEnd_8371963 4298841040657133389960549 := by
  unfold tailWord_8371963
  simp only [CollatzResearch.WordTrace]
  refine ⟨305350576168815343291928543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203567050779210228861285695 305350576168815343291928543)
  ·
    refine ⟨458025864253223014937892815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305350576168815343291928543 458025864253223014937892815)
    ·
      refine ⟨687038796379834522406839223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458025864253223014937892815 687038796379834522406839223)
      ·
        refine ⟨1030558194569751783610258835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687038796379834522406839223 1030558194569751783610258835)
        ·
          refine ⟨1545837291854627675415388253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030558194569751783610258835 1545837291854627675415388253)
          ·
            refine ⟨579688984445485378280770595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1545837291854627675415388253 579688984445485378280770595)
            ·
              refine ⟨869533476668228067421155893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579688984445485378280770595 869533476668228067421155893)
              ·
                refine ⟨81518763437646381320733365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869533476668228067421155893 81518763437646381320733365)
                ·
                  refine ⟨7642384072279348248818753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81518763437646381320733365 7642384072279348248818753)
                  ·
                    refine ⟨5731788054209511186614065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7642384072279348248818753 5731788054209511186614065)
                    ·
                      refine ⟨4298841040657133389960549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731788054209511186614065 4298841040657133389960549)
                      ·
                        rfl

theorem cell23_8371963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2, 2].length) (baseStart_8371963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371963 prefixEnd_8371963 := by exact prefixLift 8371963
  have htrace : WordTrace (prefixWord ++ tailWord_8371963) baseStart_8371963 baseEnd_8371963 := by
    simpa [prefixWord, tailWord_8371963, baseEnd_8371963] using wordTrace_append hprefix tailTrace_8371963
  have hstable : (prefixWord ++ tailWord_8371963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371963).length < 2 ^ (prefixWord ++ tailWord_8371963).sum := by decide
  have hdescent : baseEnd_8371963 < baseStart_8371963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8371976 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_8371976 : Nat := 118140960795 + 8371976 * 2 ^ 59
def prefixEnd_8371976 : Nat := 4983230072969 + 3 ^ 40 * 8371976 * 2
def baseEnd_8371976 : Nat := 4298847715905641839097989

theorem tailTrace_8371976 : CollatzResearch.WordTrace tailWord_8371976 prefixEnd_8371976 4298847715905641839097989 := by
  unfold tailWord_8371976
  simp only [CollatzResearch.WordTrace]
  refine ⟨152675525158884123256075891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203567366878512164341434521 152675525158884123256075891)
  ·
    refine ⟨229013287738326184884113837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152675525158884123256075891 229013287738326184884113837)
    ·
      refine ⟨85879982901872319331542689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229013287738326184884113837 85879982901872319331542689)
      ·
        refine ⟨64409987176404239498657017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85879982901872319331542689 64409987176404239498657017)
        ·
          refine ⟨48307490382303179623992763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64409987176404239498657017 48307490382303179623992763)
          ·
            refine ⟨72461235573454769435989145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48307490382303179623992763 72461235573454769435989145)
            ·
              refine ⟨54345926680091077076991859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72461235573454769435989145 54345926680091077076991859)
              ·
                refine ⟨81518890020136615615487789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54345926680091077076991859 81518890020136615615487789)
                ·
                  refine ⟨30569583757551230855807921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81518890020136615615487789 30569583757551230855807921)
                  ·
                    refine ⟨22927187818163423141855941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30569583757551230855807921 22927187818163423141855941)
                    ·
                      refine ⟨4298847715905641839097989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22927187818163423141855941 4298847715905641839097989)
                      ·
                        rfl

theorem cell23_8371976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_8371976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8371976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8371976 prefixEnd_8371976 := by exact prefixLift 8371976
  have htrace : WordTrace (prefixWord ++ tailWord_8371976) baseStart_8371976 baseEnd_8371976 := by
    simpa [prefixWord, tailWord_8371976, baseEnd_8371976] using wordTrace_append hprefix tailTrace_8371976
  have hstable : (prefixWord ++ tailWord_8371976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8371976).length < 2 ^ (prefixWord ++ tailWord_8371976).sum := by decide
  have hdescent : baseEnd_8371976 < baseStart_8371976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8371976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372014 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_8372014 : Nat := 118140960795 + 8372014 * 2 ^ 59
def prefixEnd_8372014 : Nat := 4983230072969 + 3 ^ 40 * 8372014 * 2
def baseEnd_8372014 : Nat := 4298867228170512690422815

theorem tailTrace_8372014 : CollatzResearch.WordTrace tailWord_8372014 prefixEnd_8372014 4298867228170512690422815 := by
  unfold tailWord_8372014
  simp only [CollatzResearch.WordTrace]
  refine ⟨38169054536453822375254387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203568290861087052668023397 38169054536453822375254387)
  ·
    refine ⟨57253581804680733562881581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38169054536453822375254387 57253581804680733562881581)
    ·
      refine ⟨21470093176755275086080593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57253581804680733562881581 21470093176755275086080593)
      ·
        refine ⟨16102569882566456314560445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21470093176755275086080593 16102569882566456314560445)
        ·
          refine ⟨6038463705962421117960167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16102569882566456314560445 6038463705962421117960167)
          ·
            refine ⟨9057695558943631676940251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038463705962421117960167 9057695558943631676940251)
            ·
              refine ⟨13586543338415447515410377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9057695558943631676940251 13586543338415447515410377)
              ·
                refine ⟨10189907503811585636557783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13586543338415447515410377 10189907503811585636557783)
                ·
                  refine ⟨15284861255717378454836675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10189907503811585636557783 15284861255717378454836675)
                  ·
                    refine ⟨22927291883576067682255013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15284861255717378454836675 22927291883576067682255013)
                    ·
                      refine ⟨4298867228170512690422815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22927291883576067682255013 4298867228170512690422815)
                      ·
                        rfl

theorem cell23_8372014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_8372014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372014 prefixEnd_8372014 := by exact prefixLift 8372014
  have htrace : WordTrace (prefixWord ++ tailWord_8372014) baseStart_8372014 baseEnd_8372014 := by
    simpa [prefixWord, tailWord_8372014, baseEnd_8372014] using wordTrace_append hprefix tailTrace_8372014
  have hstable : (prefixWord ++ tailWord_8372014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372014).length < 2 ^ (prefixWord ++ tailWord_8372014).sum := by decide
  have hdescent : baseEnd_8372014 < baseStart_8372014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372030 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_8372030 : Nat := 118140960795 + 8372030 * 2 ^ 59
def prefixEnd_8372030 : Nat := 4983230072969 + 3 ^ 40 * 8372030 * 2
def baseEnd_8372030 : Nat := 4298875443860984627822741

theorem tailTrace_8372030 : CollatzResearch.WordTrace tailWord_8372030 prefixEnd_8372030 4298875443860984627822741 := by
  unfold tailWord_8372030
  simp only [CollatzResearch.WordTrace]
  refine ⟨38169127482446576716827193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203568679906381742489745029 38169127482446576716827193)
  ·
    refine ⟨28626845611834932537620395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38169127482446576716827193 28626845611834932537620395)
    ·
      refine ⟨42940268417752398806430593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28626845611834932537620395 42940268417752398806430593)
      ·
        refine ⟨32205201313314299104822945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42940268417752398806430593 32205201313314299104822945)
        ·
          refine ⟨24153900984985724328617209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32205201313314299104822945 24153900984985724328617209)
          ·
            refine ⟨18115425738739293246462907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24153900984985724328617209 18115425738739293246462907)
            ·
              refine ⟨27173138608108939869694361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18115425738739293246462907 27173138608108939869694361)
              ·
                refine ⟨20379853956081704902270771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27173138608108939869694361 20379853956081704902270771)
                ·
                  refine ⟨30569780934122557353406157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20379853956081704902270771 30569780934122557353406157)
                  ·
                    refine ⟨11463667850295959007527309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30569780934122557353406157 11463667850295959007527309)
                    ·
                      refine ⟨4298875443860984627822741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11463667850295959007527309 4298875443860984627822741)
                      ·
                        rfl

theorem cell23_8372030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_8372030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372030 prefixEnd_8372030 := by exact prefixLift 8372030
  have htrace : WordTrace (prefixWord ++ tailWord_8372030) baseStart_8372030 baseEnd_8372030 := by
    simpa [prefixWord, tailWord_8372030, baseEnd_8372030] using wordTrace_append hprefix tailTrace_8372030
  have hstable : (prefixWord ++ tailWord_8372030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372030).length < 2 ^ (prefixWord ++ tailWord_8372030).sum := by decide
  have hdescent : baseEnd_8372030 < baseStart_8372030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372076 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 9]
def baseStart_8372076 : Nat := 118140960795 + 8372076 * 2 ^ 59
def prefixEnd_8372076 : Nat := 4983230072969 + 3 ^ 40 * 8372076 * 2
def baseEnd_8372076 : Nat := 477655451552343494205281

theorem tailTrace_8372076 : CollatzResearch.WordTrace tailWord_8372076 prefixEnd_8372076 477655451552343494205281 := by
  unfold tailWord_8372076
  simp only [CollatzResearch.WordTrace]
  refine ⟨152677348808702981795396041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203569798411603975727194721 152677348808702981795396041)
  ·
    refine ⟨114508011606527236346547031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152677348808702981795396041 114508011606527236346547031)
    ·
      refine ⟨171762017409790854519820547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114508011606527236346547031 171762017409790854519820547)
      ·
        refine ⟨257643026114686281779730821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171762017409790854519820547 257643026114686281779730821)
        ·
          refine ⟨48308067396503677833699529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257643026114686281779730821 48308067396503677833699529)
          ·
            refine ⟨36231050547377758375274647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48308067396503677833699529 36231050547377758375274647)
            ·
              refine ⟨54346575821066637562911971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36231050547377758375274647 54346575821066637562911971)
              ·
                refine ⟨81519863731599956344367957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54346575821066637562911971 81519863731599956344367957)
                ·
                  refine ⟨477655451552343494205281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81519863731599956344367957 477655451552343494205281)
                  ·
                    rfl

theorem cell23_8372076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_8372076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372076 prefixEnd_8372076 := by exact prefixLift 8372076
  have htrace : WordTrace (prefixWord ++ tailWord_8372076) baseStart_8372076 baseEnd_8372076 := by
    simpa [prefixWord, tailWord_8372076, baseEnd_8372076] using wordTrace_append hprefix tailTrace_8372076
  have hstable : (prefixWord ++ tailWord_8372076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372076).length < 2 ^ (prefixWord ++ tailWord_8372076).sum := by decide
  have hdescent : baseEnd_8372076 < baseStart_8372076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372113 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_8372113 : Nat := 118140960795 + 8372113 * 2 ^ 59
def prefixEnd_8372113 : Nat := 4983230072969 + 3 ^ 40 * 8372113 * 2
def baseEnd_8372113 : Nat := 4298918062755307803084859

theorem tailTrace_8372113 : CollatzResearch.WordTrace tailWord_8372113 prefixEnd_8372113 4298918062755307803084859 := by
  unfold tailWord_8372113
  simp only [CollatzResearch.WordTrace]
  refine ⟨305356047118271918909888993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203570698078847945939925995 305356047118271918909888993)
  ·
    refine ⟨229017035338703939182416745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305356047118271918909888993 229017035338703939182416745)
    ·
      refine ⟨171762776504027954386812559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229017035338703939182416745 171762776504027954386812559)
      ·
        refine ⟨257644164756041931580218839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171762776504027954386812559 257644164756041931580218839)
        ·
          refine ⟨386466247134062897370328259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257644164756041931580218839 386466247134062897370328259)
          ·
            refine ⟨579699370701094346055492389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386466247134062897370328259 579699370701094346055492389)
            ·
              refine ⟨108693632006455189885404823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 579699370701094346055492389 108693632006455189885404823)
              ·
                refine ⟨163040448009682784828107235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108693632006455189885404823 163040448009682784828107235)
                ·
                  refine ⟨244560672014524177242160853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163040448009682784828107235 244560672014524177242160853)
                  ·
                    refine ⟨5731890750340410404113145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 244560672014524177242160853 5731890750340410404113145)
                    ·
                      refine ⟨4298918062755307803084859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5731890750340410404113145 4298918062755307803084859)
                      ·
                        rfl

theorem cell23_8372113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_8372113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372113 prefixEnd_8372113 := by exact prefixLift 8372113
  have htrace : WordTrace (prefixWord ++ tailWord_8372113) baseStart_8372113 baseEnd_8372113 := by
    simpa [prefixWord, tailWord_8372113, baseEnd_8372113] using wordTrace_append hprefix tailTrace_8372113
  have hstable : (prefixWord ++ tailWord_8372113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372113).length < 2 ^ (prefixWord ++ tailWord_8372113).sum := by decide
  have hdescent : baseEnd_8372113 < baseStart_8372113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372143 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_8372143 : Nat := 118140960795 + 8372143 * 2 ^ 59
def prefixEnd_8372143 : Nat := 4983230072969 + 3 ^ 40 * 8372143 * 2
def baseEnd_8372143 : Nat := 4298933467174942685709721

theorem tailTrace_8372143 : CollatzResearch.WordTrace tailWord_8372143 prefixEnd_8372143 4298933467174942685709721 := by
  unfold tailWord_8372143
  simp only [CollatzResearch.WordTrace]
  refine ⟨305357141308163234033481083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203571427538775489355654055 305357141308163234033481083)
  ·
    refine ⟨458035711962244851050221625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305357141308163234033481083 458035711962244851050221625)
    ·
      refine ⟨343526783971683638287666219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458035711962244851050221625 343526783971683638287666219)
      ·
        refine ⟨515290175957525457431499329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343526783971683638287666219 515290175957525457431499329)
        ·
          refine ⟨386467631968144093073624497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515290175957525457431499329 386467631968144093073624497)
          ·
            refine ⟨289850723976108069805218373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386467631968144093073624497 289850723976108069805218373)
            ·
              refine ⟨54347010745520263088478445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289850723976108069805218373 54347010745520263088478445)
              ·
                refine ⟨20380129029570098658179417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54347010745520263088478445 20380129029570098658179417)
                ·
                  refine ⟨15285096772177573993634563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20380129029570098658179417 15285096772177573993634563)
                  ·
                    refine ⟨22927645158266360990451845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15285096772177573993634563 22927645158266360990451845)
                    ·
                      refine ⟨4298933467174942685709721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22927645158266360990451845 4298933467174942685709721)
                      ·
                        rfl

theorem cell23_8372143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_8372143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372143 prefixEnd_8372143 := by exact prefixLift 8372143
  have htrace : WordTrace (prefixWord ++ tailWord_8372143) baseStart_8372143 baseEnd_8372143 := by
    simpa [prefixWord, tailWord_8372143, baseEnd_8372143] using wordTrace_append hprefix tailTrace_8372143
  have hstable : (prefixWord ++ tailWord_8372143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372143).length < 2 ^ (prefixWord ++ tailWord_8372143).sum := by decide
  have hdescent : baseEnd_8372143 < baseStart_8372143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372170 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_8372170 : Nat := 118140960795 + 8372170 * 2 ^ 59
def prefixEnd_8372170 : Nat := 4983230072969 + 3 ^ 40 * 8372170 * 2
def baseEnd_8372170 : Nat := 1432982443717538026690699

theorem tailTrace_8372170 : CollatzResearch.WordTrace tailWord_8372170 prefixEnd_8372170 1432982443717538026690699 := by
  unfold tailWord_8372170
  simp only [CollatzResearch.WordTrace]
  refine ⟨76339531519766354411178491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203572084052710278429809309 76339531519766354411178491)
  ·
    refine ⟨114509297279649531616767737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76339531519766354411178491 114509297279649531616767737)
    ·
      refine ⟨85881972959737148712575803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114509297279649531616767737 85881972959737148712575803)
      ·
        refine ⟨128822959439605723068863705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85881972959737148712575803 128822959439605723068863705)
        ·
          refine ⟨96617219579704292301647779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128822959439605723068863705 96617219579704292301647779)
          ·
            refine ⟨144925829369556438452471669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96617219579704292301647779 144925829369556438452471669)
            ·
              refine ⟨13586796503395916104919219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144925829369556438452471669 13586796503395916104919219)
              ·
                refine ⟨20380194755093874157378829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13586796503395916104919219 20380194755093874157378829)
                ·
                  refine ⟨7642573033160202809017061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20380194755093874157378829 7642573033160202809017061)
                  ·
                    refine ⟨1432982443717538026690699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7642573033160202809017061 1432982443717538026690699)
                    ·
                      rfl

theorem cell23_8372170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_8372170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372170 prefixEnd_8372170 := by exact prefixLift 8372170
  have htrace : WordTrace (prefixWord ++ tailWord_8372170) baseStart_8372170 baseEnd_8372170 := by
    simpa [prefixWord, tailWord_8372170, baseEnd_8372170] using wordTrace_append hprefix tailTrace_8372170
  have hstable : (prefixWord ++ tailWord_8372170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372170).length < 2 ^ (prefixWord ++ tailWord_8372170).sum := by decide
  have hdescent : baseEnd_8372170 < baseStart_8372170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372180 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_8372180 : Nat := 118140960795 + 8372180 * 2 ^ 59
def prefixEnd_8372180 : Nat := 4983230072969 + 3 ^ 40 * 8372180 * 2
def baseEnd_8372180 : Nat := 4298952465959159040947051

theorem tailTrace_8372180 : CollatzResearch.WordTrace tailWord_8372180 prefixEnd_8372180 4298952465959159040947051 := by
  unfold tailWord_8372180
  simp only [CollatzResearch.WordTrace]
  refine ⟨152679245404514594676288997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203572327206019459568385329 152679245404514594676288997)
  ·
    refine ⟨28627358513346486501804187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152679245404514594676288997 28627358513346486501804187)
    ·
      refine ⟨42941037770019729752706281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28627358513346486501804187 42941037770019729752706281)
      ·
        refine ⟨32205778327514797314529711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42941037770019729752706281 32205778327514797314529711)
        ·
          refine ⟨48308667491272195971794567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32205778327514797314529711 48308667491272195971794567)
          ·
            refine ⟨72463001236908293957691851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48308667491272195971794567 72463001236908293957691851)
            ·
              refine ⟨108694501855362440936537777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72463001236908293957691851 108694501855362440936537777)
              ·
                refine ⟨81520876391521830702403333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108694501855362440936537777 81520876391521830702403333)
                ·
                  refine ⟨15285164323410343256700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81520876391521830702403333 15285164323410343256700625)
                  ·
                    refine ⟨11463873242557757442525469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15285164323410343256700625 11463873242557757442525469)
                    ·
                      refine ⟨4298952465959159040947051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11463873242557757442525469 4298952465959159040947051)
                      ·
                        rfl

theorem cell23_8372180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_8372180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372180 prefixEnd_8372180 := by exact prefixLift 8372180
  have htrace : WordTrace (prefixWord ++ tailWord_8372180) baseStart_8372180 baseEnd_8372180 := by
    simpa [prefixWord, tailWord_8372180, baseEnd_8372180] using wordTrace_append hprefix tailTrace_8372180
  have hstable : (prefixWord ++ tailWord_8372180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372180).length < 2 ^ (prefixWord ++ tailWord_8372180).sum := by decide
  have hdescent : baseEnd_8372180 < baseStart_8372180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372183 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 6]
def baseStart_8372183 : Nat := 118140960795 + 8372183 * 2 ^ 59
def prefixEnd_8372183 : Nat := 4983230072969 + 3 ^ 40 * 8372183 * 2
def baseEnd_8372183 : Nat := 477661556266791392134393

theorem tailTrace_8372183 : CollatzResearch.WordTrace tailWord_8372183 prefixEnd_8372183 477661556266791392134393 := by
  unfold tailWord_8372183
  simp only [CollatzResearch.WordTrace]
  refine ⟨305358600228018320864937203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203572400152012213909958135 305358600228018320864937203)
  ·
    refine ⟨458037900342027481297405805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305358600228018320864937203 458037900342027481297405805)
    ·
      refine ⟨171764212628260305486527177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458037900342027481297405805 171764212628260305486527177)
      ·
        refine ⟨128823159471195229114895383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171764212628260305486527177 128823159471195229114895383)
        ·
          refine ⟨193234739206792843672343075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128823159471195229114895383 193234739206792843672343075)
          ·
            refine ⟨289852108810189265508514613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193234739206792843672343075 289852108810189265508514613)
            ·
              refine ⟨27173635200955243641423245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289852108810189265508514613 27173635200955243641423245)
              ·
                refine ⟨10190113200358216365533717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27173635200955243641423245 10190113200358216365533717)
                ·
                  refine ⟨477661556266791392134393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10190113200358216365533717 477661556266791392134393)
                  ·
                    rfl

theorem cell23_8372183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 6].length) (baseStart_8372183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372183 prefixEnd_8372183 := by exact prefixLift 8372183
  have htrace : WordTrace (prefixWord ++ tailWord_8372183) baseStart_8372183 baseEnd_8372183 := by
    simpa [prefixWord, tailWord_8372183, baseEnd_8372183] using wordTrace_append hprefix tailTrace_8372183
  have hstable : (prefixWord ++ tailWord_8372183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372183).length < 2 ^ (prefixWord ++ tailWord_8372183).sum := by decide
  have hdescent : baseEnd_8372183 < baseStart_8372183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372193 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_8372193 : Nat := 118140960795 + 8372193 * 2 ^ 59
def prefixEnd_8372193 : Nat := 4983230072969 + 3 ^ 40 * 8372193 * 2
def baseEnd_8372193 : Nat := 4298959141207667490084491

theorem tailTrace_8372193 : CollatzResearch.WordTrace tailWord_8372193 prefixEnd_8372193 4298959141207667490084491 := by
  unfold tailWord_8372193
  simp only [CollatzResearch.WordTrace]
  refine ⟨305358964957982092572801233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203572643305321395048534155 305358964957982092572801233)
  ·
    refine ⟨229019223718486569429600925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305358964957982092572801233 229019223718486569429600925)
    ·
      refine ⟨85882208894432463536100347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229019223718486569429600925 85882208894432463536100347)
      ·
        refine ⟨128823313341648695304150521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85882208894432463536100347 128823313341648695304150521)
        ·
          refine ⟨96617485006236521478112891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128823313341648695304150521 96617485006236521478112891)
          ·
            refine ⟨144926227509354782217169337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96617485006236521478112891 144926227509354782217169337)
            ·
              refine ⟨108694670632016086662877003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144926227509354782217169337 108694670632016086662877003)
              ·
                refine ⟨163042005948024129994315505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108694670632016086662877003 163042005948024129994315505)
                ·
                  refine ⟨122281504461018097495736629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163042005948024129994315505 122281504461018097495736629)
                  ·
                    refine ⟨11463891043220446640225309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122281504461018097495736629 11463891043220446640225309)
                    ·
                      refine ⟨4298959141207667490084491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11463891043220446640225309 4298959141207667490084491)
                      ·
                        rfl

theorem cell23_8372193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_8372193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372193 prefixEnd_8372193 := by exact prefixLift 8372193
  have htrace : WordTrace (prefixWord ++ tailWord_8372193) baseStart_8372193 baseEnd_8372193 := by
    simpa [prefixWord, tailWord_8372193, baseEnd_8372193] using wordTrace_append hprefix tailTrace_8372193
  have hstable : (prefixWord ++ tailWord_8372193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372193).length < 2 ^ (prefixWord ++ tailWord_8372193).sum := by decide
  have hdescent : baseEnd_8372193 < baseStart_8372193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372194 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_8372194 : Nat := 118140960795 + 8372194 * 2 ^ 59
def prefixEnd_8372194 : Nat := 4983230072969 + 3 ^ 40 * 8372194 * 2
def baseEnd_8372194 : Nat := 4298959654688321986171987

theorem tailTrace_8372194 : CollatzResearch.WordTrace tailWord_8372194 prefixEnd_8372194 4298959654688321986171987 := by
  unfold tailWord_8372194
  simp only [CollatzResearch.WordTrace]
  refine ⟨76339750357744617435896909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203572667620652313162391757 76339750357744617435896909)
  ·
    refine ⟨28627406384154231538461341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76339750357744617435896909 28627406384154231538461341)
    ·
      refine ⟨10735277394057836826923003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28627406384154231538461341 10735277394057836826923003)
      ·
        refine ⟨16102916091086755240384505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10735277394057836826923003 16102916091086755240384505)
        ·
          refine ⟨12077187068315066430288379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16102916091086755240384505 12077187068315066430288379)
          ·
            refine ⟨18115780602472599645432569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077187068315066430288379 18115780602472599645432569)
            ·
              refine ⟨13586835451854449734074427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18115780602472599645432569 13586835451854449734074427)
              ·
                refine ⟨20380253177781674601111641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13586835451854449734074427 20380253177781674601111641)
                ·
                  refine ⟨15285189883336255950833731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20380253177781674601111641 15285189883336255950833731)
                  ·
                    refine ⟨22927784825004383926250597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15285189883336255950833731 22927784825004383926250597)
                    ·
                      refine ⟨4298959654688321986171987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22927784825004383926250597 4298959654688321986171987)
                      ·
                        rfl

theorem cell23_8372194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_8372194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372194 prefixEnd_8372194 := by exact prefixLift 8372194
  have htrace : WordTrace (prefixWord ++ tailWord_8372194) baseStart_8372194 baseEnd_8372194 := by
    simpa [prefixWord, tailWord_8372194, baseEnd_8372194] using wordTrace_append hprefix tailTrace_8372194
  have hstable : (prefixWord ++ tailWord_8372194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372194).length < 2 ^ (prefixWord ++ tailWord_8372194).sum := by decide
  have hdescent : baseEnd_8372194 < baseStart_8372194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372243 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 1, 6]
def baseStart_8372243 : Nat := 118140960795 + 8372243 * 2 ^ 59
def prefixEnd_8372243 : Nat := 4983230072969 + 3 ^ 40 * 8372243 * 2
def baseEnd_8372243 : Nat := 1432994938413464098153087

theorem tailTrace_8372243 : CollatzResearch.WordTrace tailWord_8372243 prefixEnd_8372243 1432994938413464098153087 := by
  unfold tailWord_8372243
  simp only [CollatzResearch.WordTrace]
  refine ⟨305360788607800951112121383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203573859071867300741414255 305360788607800951112121383)
  ·
    refine ⟨458041182911701426668182075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305360788607800951112121383 458041182911701426668182075)
    ·
      refine ⟨687061774367552140002273113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458041182911701426668182075 687061774367552140002273113)
      ·
        refine ⟨515296330775664105001704835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687061774367552140002273113 515296330775664105001704835)
        ·
          refine ⟨772944496163496157502557253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515296330775664105001704835 772944496163496157502557253)
          ·
            refine ⟨144927093030655529531729485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 772944496163496157502557253 144927093030655529531729485)
            ·
              refine ⟨54347659886495823574398557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144927093030655529531729485 54347659886495823574398557)
              ·
                refine ⟨20380372457435933840399459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54347659886495823574398557 20380372457435933840399459)
                ·
                  refine ⟨30570558686153900760599189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20380372457435933840399459 30570558686153900760599189)
                  ·
                    refine ⟨1432994938413464098153087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30570558686153900760599189 1432994938413464098153087)
                    ·
                      rfl

theorem cell23_8372243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 6].length) (baseStart_8372243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372243 prefixEnd_8372243 := by exact prefixLift 8372243
  have htrace : WordTrace (prefixWord ++ tailWord_8372243) baseStart_8372243 baseEnd_8372243 := by
    simpa [prefixWord, tailWord_8372243, baseEnd_8372243] using wordTrace_append hprefix tailTrace_8372243
  have hstable : (prefixWord ++ tailWord_8372243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372243).length < 2 ^ (prefixWord ++ tailWord_8372243).sum := by decide
  have hdescent : baseEnd_8372243 < baseStart_8372243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372250 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_8372250 : Nat := 118140960795 + 8372250 * 2 ^ 59
def prefixEnd_8372250 : Nat := 4983230072969 + 3 ^ 40 * 8372250 * 2
def baseEnd_8372250 : Nat := 4298988409604973767071729

theorem tailTrace_8372250 : CollatzResearch.WordTrace tailWord_8372250 prefixEnd_8372250 4298988409604973767071729 := by
  unfold tailWord_8372250
  simp only [CollatzResearch.WordTrace]
  refine ⟨76340260979693897826906551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203574029279183727538417469 76340260979693897826906551)
  ·
    refine ⟨114510391469540846740359827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76340260979693897826906551 114510391469540846740359827)
    ·
      refine ⟨171765587204311270110539741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114510391469540846740359827 171765587204311270110539741)
      ·
        refine ⟨64412095201616726291452403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171765587204311270110539741 64412095201616726291452403)
        ·
          refine ⟨96618142802425089437178605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64412095201616726291452403 96618142802425089437178605)
          ·
            refine ⟨36231803550909408538941977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96618142802425089437178605 36231803550909408538941977)
            ·
              refine ⟨27173852663182056404206483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36231803550909408538941977 27173852663182056404206483)
              ·
                refine ⟨40760778994773084606309725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27173852663182056404206483 40760778994773084606309725)
                ·
                  refine ⟨15285292123039906727366147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40760778994773084606309725 15285292123039906727366147)
                  ·
                    refine ⟨22927938184559860091049221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15285292123039906727366147 22927938184559860091049221)
                    ·
                      refine ⟨4298988409604973767071729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22927938184559860091049221 4298988409604973767071729)
                      ·
                        rfl

theorem cell23_8372250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_8372250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372250 prefixEnd_8372250 := by exact prefixLift 8372250
  have htrace : WordTrace (prefixWord ++ tailWord_8372250) baseStart_8372250 baseEnd_8372250 := by
    simpa [prefixWord, tailWord_8372250, baseEnd_8372250] using wordTrace_append hprefix tailTrace_8372250
  have hstable : (prefixWord ++ tailWord_8372250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372250).length < 2 ^ (prefixWord ++ tailWord_8372250).sum := by decide
  have hdescent : baseEnd_8372250 < baseStart_8372250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372264 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_8372264 : Nat := 118140960795 + 8372264 * 2 ^ 59
def prefixEnd_8372264 : Nat := 4983230072969 + 3 ^ 40 * 8372264 * 2
def baseEnd_8372264 : Nat := 1432998532778045570765555

theorem tailTrace_8372264 : CollatzResearch.WordTrace tailWord_8372264 prefixEnd_8372264 1432998532778045570765555 := by
  unfold tailWord_8372264
  simp only [CollatzResearch.WordTrace]
  refine ⟨152680777270362435849317923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203574369693816581132423897 152680777270362435849317923)
  ·
    refine ⟨229021165905543653773976885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152680777270362435849317923 229021165905543653773976885)
    ·
      refine ⟨21470734303644717541310333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229021165905543653773976885 21470734303644717541310333)
      ·
        refine ⟨8051525363866769077991375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21470734303644717541310333 8051525363866769077991375)
        ·
          refine ⟨12077288045800153616987063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051525363866769077991375 12077288045800153616987063)
          ·
            refine ⟨18115932068700230425480595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077288045800153616987063 18115932068700230425480595)
            ·
              refine ⟨27173898103050345638220893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18115932068700230425480595 27173898103050345638220893)
              ·
                refine ⟨10190211788643879614332835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27173898103050345638220893 10190211788643879614332835)
                ·
                  refine ⟨15285317682965819421499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10190211788643879614332835 15285317682965819421499253)
                  ·
                    refine ⟨1432998532778045570765555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15285317682965819421499253 1432998532778045570765555)
                    ·
                      rfl

theorem cell23_8372264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_8372264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372264 prefixEnd_8372264 := by exact prefixLift 8372264
  have htrace : WordTrace (prefixWord ++ tailWord_8372264) baseStart_8372264 baseEnd_8372264 := by
    simpa [prefixWord, tailWord_8372264, baseEnd_8372264] using wordTrace_append hprefix tailTrace_8372264
  have hstable : (prefixWord ++ tailWord_8372264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372264).length < 2 ^ (prefixWord ++ tailWord_8372264).sum := by decide
  have hdescent : baseEnd_8372264 < baseStart_8372264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372273 : List Nat := [1, 2, 2, 3, 1, 4, 10]
def baseStart_8372273 : Nat := 118140960795 + 8372273 * 2 ^ 59
def prefixEnd_8372273 : Nat := 4983230072969 + 3 ^ 40 * 8372273 * 2
def baseEnd_8372273 : Nat := 53074076785926261445483

theorem tailTrace_8372273 : CollatzResearch.WordTrace tailWord_8372273 prefixEnd_8372273 53074076785926261445483 := by
  unfold tailWord_8372273
  simp only [CollatzResearch.WordTrace]
  refine ⟨305361882797692266235713473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203574588531794844157142315 305361882797692266235713473)
  ·
    refine ⟨229021412098269199676785105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305361882797692266235713473 229021412098269199676785105)
    ·
      refine ⟨171766059073701899757588829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229021412098269199676785105 171766059073701899757588829)
      ·
        refine ⟨64412272152638212409095811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171766059073701899757588829 64412272152638212409095811)
        ·
          refine ⟨96618408228957318613643717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64412272152638212409095811 96618408228957318613643717)
          ·
            refine ⟨18115951542929497240058197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96618408228957318613643717 18115951542929497240058197)
            ·
              refine ⟨53074076785926261445483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18115951542929497240058197 53074076785926261445483)
              ·
                rfl

theorem cell23_8372273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 10].length) (baseStart_8372273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372273 prefixEnd_8372273 := by exact prefixLift 8372273
  have htrace : WordTrace (prefixWord ++ tailWord_8372273) baseStart_8372273 baseEnd_8372273 := by
    simpa [prefixWord, tailWord_8372273, baseEnd_8372273] using wordTrace_append hprefix tailTrace_8372273
  have hstable : (prefixWord ++ tailWord_8372273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372273).length < 2 ^ (prefixWord ++ tailWord_8372273).sum := by decide
  have hdescent : baseEnd_8372273 < baseStart_8372273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372277 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_8372277 : Nat := 118140960795 + 8372277 * 2 ^ 59
def prefixEnd_8372277 : Nat := 4983230072969 + 3 ^ 40 * 8372277 * 2
def baseEnd_8372277 : Nat := 1433000757860881720478035

theorem tailTrace_8372277 : CollatzResearch.WordTrace tailWord_8372277 prefixEnd_8372277 1433000757860881720478035 := by
  unfold tailWord_8372277
  simp only [CollatzResearch.WordTrace]
  refine ⟨305362028689677774918859085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203574685793118516612572723 305362028689677774918859085)
  ·
    refine ⟨114510760758629165594572157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305362028689677774918859085 114510760758629165594572157)
    ·
      refine ⟨42941535284485937097964559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114510760758629165594572157 42941535284485937097964559)
      ·
        refine ⟨64412302926728905646946839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42941535284485937097964559 64412302926728905646946839)
        ·
          refine ⟨96618454390093358470420259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64412302926728905646946839 96618454390093358470420259)
          ·
            refine ⟨144927681585140037705630389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96618454390093358470420259 144927681585140037705630389)
            ·
              refine ⟨13586970148606878534902849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144927681585140037705630389 13586970148606878534902849)
              ·
                refine ⟨10190227611455158901177137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13586970148606878534902849 10190227611455158901177137)
                ·
                  refine ⟨7642670708591369175882853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10190227611455158901177137 7642670708591369175882853)
                  ·
                    refine ⟨1433000757860881720478035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7642670708591369175882853 1433000757860881720478035)
                    ·
                      rfl

theorem cell23_8372277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_8372277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372277 prefixEnd_8372277 := by exact prefixLift 8372277
  have htrace : WordTrace (prefixWord ++ tailWord_8372277) baseStart_8372277 baseEnd_8372277 := by
    simpa [prefixWord, tailWord_8372277, baseEnd_8372277] using wordTrace_append hprefix tailTrace_8372277
  have hstable : (prefixWord ++ tailWord_8372277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372277).length < 2 ^ (prefixWord ++ tailWord_8372277).sum := by decide
  have hdescent : baseEnd_8372277 < baseStart_8372277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372284 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_8372284 : Nat := 118140960795 + 8372284 * 2 ^ 59
def prefixEnd_8372284 : Nat := 4983230072969 + 3 ^ 40 * 8372284 * 2
def baseEnd_8372284 : Nat := 4299005867947226634046573

theorem tailTrace_8372284 : CollatzResearch.WordTrace tailWord_8372284 prefixEnd_8372284 4299005867947226634046573 := by
  unfold tailWord_8372284
  simp only [CollatzResearch.WordTrace]
  refine ⟨152681142000326207557181953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203574856000434943409575937 152681142000326207557181953)
  ·
    refine ⟨114510856500244655667886465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152681142000326207557181953 114510856500244655667886465)
    ·
      refine ⟨85883142375183491750914849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114510856500244655667886465 85883142375183491750914849)
      ·
        refine ⟨64412356781387618813186137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85883142375183491750914849 64412356781387618813186137)
        ·
          refine ⟨48309267586040714109889603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64412356781387618813186137 48309267586040714109889603)
          ·
            refine ⟨72463901379061071164834405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48309267586040714109889603 72463901379061071164834405)
            ·
              refine ⟨13586981508573950843406451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72463901379061071164834405 13586981508573950843406451)
              ·
                refine ⟨20380472262860926265109677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13586981508573950843406451 20380472262860926265109677)
                ·
                  refine ⟨7642677098572847349416129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20380472262860926265109677 7642677098572847349416129)
                  ·
                    refine ⟨5732007823929635512062097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7642677098572847349416129 5732007823929635512062097)
                    ·
                      refine ⟨4299005867947226634046573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732007823929635512062097 4299005867947226634046573)
                      ·
                        rfl

theorem cell23_8372284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_8372284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372284 prefixEnd_8372284 := by exact prefixLift 8372284
  have htrace : WordTrace (prefixWord ++ tailWord_8372284) baseStart_8372284 baseEnd_8372284 := by
    simpa [prefixWord, tailWord_8372284, baseEnd_8372284] using wordTrace_append hprefix tailTrace_8372284
  have hstable : (prefixWord ++ tailWord_8372284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372284).length < 2 ^ (prefixWord ++ tailWord_8372284).sum := by decide
  have hdescent : baseEnd_8372284 < baseStart_8372284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372313 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_8372313 : Nat := 118140960795 + 8372313 * 2 ^ 59
def prefixEnd_8372313 : Nat := 4983230072969 + 3 ^ 40 * 8372313 * 2
def baseEnd_8372313 : Nat := 4299020758886207020583939

theorem tailTrace_8372313 : CollatzResearch.WordTrace tailWord_8372313 prefixEnd_8372313 4299020758886207020583939 := by
  unfold tailWord_8372313
  simp only [CollatzResearch.WordTrace]
  refine ⟨305363341717547353067169593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203575561145031568711446395 305363341717547353067169593)
  ·
    refine ⟨229022506288160514800377195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305363341717547353067169593 229022506288160514800377195)
    ·
      refine ⟨343533759432240772200565793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229022506288160514800377195 343533759432240772200565793)
      ·
        refine ⟨257650319574180579150424345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343533759432240772200565793 257650319574180579150424345)
        ·
          refine ⟨193237739680635434362818259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257650319574180579150424345 193237739680635434362818259)
          ·
            refine ⟨289856609520953151544227389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193237739680635434362818259 289856609520953151544227389)
            ·
              refine ⟨108696228570357431829085271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289856609520953151544227389 108696228570357431829085271)
              ·
                refine ⟨163044342855536147743627907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108696228570357431829085271 163044342855536147743627907)
                ·
                  refine ⟨244566514283304221615441861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163044342855536147743627907 244566514283304221615441861)
                  ·
                    refine ⟨45856221428119541552895349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244566514283304221615441861 45856221428119541552895349)
                    ·
                      refine ⟨4299020758886207020583939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45856221428119541552895349 4299020758886207020583939)
                      ·
                        rfl

theorem cell23_8372313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_8372313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372313 prefixEnd_8372313 := by exact prefixLift 8372313
  have htrace : WordTrace (prefixWord ++ tailWord_8372313) baseStart_8372313 baseEnd_8372313 := by
    simpa [prefixWord, tailWord_8372313, baseEnd_8372313] using wordTrace_append hprefix tailTrace_8372313
  have hstable : (prefixWord ++ tailWord_8372313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372313).length < 2 ^ (prefixWord ++ tailWord_8372313).sum := by decide
  have hdescent : baseEnd_8372313 < baseStart_8372313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372334 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_8372334 : Nat := 118140960795 + 8372334 * 2 ^ 59
def prefixEnd_8372334 : Nat := 4983230072969 + 3 ^ 40 * 8372334 * 2
def baseEnd_8372334 : Nat := 4299031541979951438421343

theorem tailTrace_8372334 : CollatzResearch.WordTrace tailWord_8372334 prefixEnd_8372334 4299031541979951438421343 := by
  unfold tailWord_8372334
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170513456308909206710507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203576071766980849102456037 38170513456308909206710507)
  ·
    refine ⟨57255770184463363810065761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38170513456308909206710507 57255770184463363810065761)
    ·
      refine ⟨42941827638347522857549321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57255770184463363810065761 42941827638347522857549321)
      ·
        refine ⟨32206370728760642143161991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42941827638347522857549321 32206370728760642143161991)
        ·
          refine ⟨48309556093140963214742987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32206370728760642143161991 48309556093140963214742987)
          ·
            refine ⟨72464334139711444822114481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48309556093140963214742987 72464334139711444822114481)
            ·
              refine ⟨54348250604783583616585861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72464334139711444822114481 54348250604783583616585861)
              ·
                refine ⟨10190296988396921928109849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54348250604783583616585861 10190296988396921928109849)
                ·
                  refine ⟨7642722741297691446082387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10190296988396921928109849 7642722741297691446082387)
                  ·
                    refine ⟨11464084111946537169123581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7642722741297691446082387 11464084111946537169123581)
                    ·
                      refine ⟨4299031541979951438421343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464084111946537169123581 4299031541979951438421343)
                      ·
                        rfl

theorem cell23_8372334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_8372334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372334 prefixEnd_8372334 := by exact prefixLift 8372334
  have htrace : WordTrace (prefixWord ++ tailWord_8372334) baseStart_8372334 baseEnd_8372334 := by
    simpa [prefixWord, tailWord_8372334, baseEnd_8372334] using wordTrace_append hprefix tailTrace_8372334
  have hstable : (prefixWord ++ tailWord_8372334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372334).length < 2 ^ (prefixWord ++ tailWord_8372334).sum := by decide
  have hdescent : baseEnd_8372334 < baseStart_8372334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372378 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_8372378 : Nat := 118140960795 + 8372378 * 2 ^ 59
def prefixEnd_8372378 : Nat := 4983230072969 + 3 ^ 40 * 8372378 * 2
def baseEnd_8372378 : Nat := 4299054135128749266271141

theorem tailTrace_8372378 : CollatzResearch.WordTrace tailWord_8372378 prefixEnd_8372378 4299054135128749266271141 := by
  unfold tailWord_8372378
  simp only [CollatzResearch.WordTrace]
  refine ⟨76341428115577967292071447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203577141641541246112190525 76341428115577967292071447)
  ·
    refine ⟨114512142173366950938107171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76341428115577967292071447 114512142173366950938107171)
    ·
      refine ⟨171768213260050426407160757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114512142173366950938107171 171768213260050426407160757)
      ·
        refine ⟨16103269993129727475671321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171768213260050426407160757 16103269993129727475671321)
        ·
          refine ⟨12077452494847295606753491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16103269993129727475671321 12077452494847295606753491)
          ·
            refine ⟨18116178742270943410130237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077452494847295606753491 18116178742270943410130237)
            ·
              refine ⟨6793567028351603778798839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18116178742270943410130237 6793567028351603778798839)
              ·
                refine ⟨10190350542527405668198259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6793567028351603778798839 10190350542527405668198259)
                ·
                  refine ⟨15285525813791108502297389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10190350542527405668198259 15285525813791108502297389)
                  ·
                    refine ⟨5732072180171665688361521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15285525813791108502297389 5732072180171665688361521)
                    ·
                      refine ⟨4299054135128749266271141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732072180171665688361521 4299054135128749266271141)
                      ·
                        rfl

theorem cell23_8372378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_8372378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372378 prefixEnd_8372378 := by exact prefixLift 8372378
  have htrace : WordTrace (prefixWord ++ tailWord_8372378) baseStart_8372378 baseEnd_8372378 := by
    simpa [prefixWord, tailWord_8372378, baseEnd_8372378] using wordTrace_append hprefix tailTrace_8372378
  have hstable : (prefixWord ++ tailWord_8372378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372378).length < 2 ^ (prefixWord ++ tailWord_8372378).sum := by decide
  have hdescent : baseEnd_8372378 < baseStart_8372378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372407 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_8372407 : Nat := 118140960795 + 8372407 * 2 ^ 59
def prefixEnd_8372407 : Nat := 4983230072969 + 3 ^ 40 * 8372407 * 2
def baseEnd_8372407 : Nat := 4299069026067729652808507

theorem tailTrace_8372407 : CollatzResearch.WordTrace tailWord_8372407 prefixEnd_8372407 4299069026067729652808507 := by
  unfold tailWord_8372407
  simp only [CollatzResearch.WordTrace]
  refine ⟨305366770179206807121091475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203577846786137871414060983 305366770179206807121091475)
  ·
    refine ⟨458050155268810210681637213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305366770179206807121091475 458050155268810210681637213)
    ·
      refine ⟨171768808225803829005613955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458050155268810210681637213 171768808225803829005613955)
      ·
        refine ⟨257653212338705743508420933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171768808225803829005613955 257653212338705743508420933)
        ·
          refine ⟨48309977313507326907828925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257653212338705743508420933 48309977313507326907828925)
          ·
            refine ⟨18116241492565247590435847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48309977313507326907828925 18116241492565247590435847)
            ·
              refine ⟨27174362238847871385653771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18116241492565247590435847 27174362238847871385653771)
              ·
                refine ⟨40761543358271807078480657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27174362238847871385653771 40761543358271807078480657)
                ·
                  refine ⟨30571157518703855308860493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40761543358271807078480657 30571157518703855308860493)
                  ·
                    refine ⟨11464184069513945740822685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30571157518703855308860493 11464184069513945740822685)
                    ·
                      refine ⟨4299069026067729652808507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464184069513945740822685 4299069026067729652808507)
                      ·
                        rfl

theorem cell23_8372407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_8372407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372407 prefixEnd_8372407 := by exact prefixLift 8372407
  have htrace : WordTrace (prefixWord ++ tailWord_8372407) baseStart_8372407 baseEnd_8372407 := by
    simpa [prefixWord, tailWord_8372407, baseEnd_8372407] using wordTrace_append hprefix tailTrace_8372407
  have hstable : (prefixWord ++ tailWord_8372407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372407).length < 2 ^ (prefixWord ++ tailWord_8372407).sum := by decide
  have hdescent : baseEnd_8372407 < baseStart_8372407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372410 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_8372410 : Nat := 118140960795 + 8372410 * 2 ^ 59
def prefixEnd_8372410 : Nat := 4983230072969 + 3 ^ 40 * 8372410 * 2
def baseEnd_8372410 : Nat := 1433023522169897713690331

theorem tailTrace_8372410 : CollatzResearch.WordTrace tailWord_8372410 prefixEnd_8372410 1433023522169897713690331 := by
  unfold tailWord_8372410
  simp only [CollatzResearch.WordTrace]
  refine ⟨76341719899548984658362671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203577919732130625755633789 76341719899548984658362671)
  ·
    refine ⟨114512579849323476987544007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76341719899548984658362671 114512579849323476987544007)
    ·
      refine ⟨171768869773985215481316011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114512579849323476987544007 171768869773985215481316011)
      ·
        refine ⟨257653304660977823221974017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171768869773985215481316011 257653304660977823221974017)
        ·
          refine ⟨193239978495733367416480513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257653304660977823221974017 193239978495733367416480513)
          ·
            refine ⟨144929983871800025562360385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193239978495733367416480513 144929983871800025562360385)
            ·
              refine ⟨108697487903850019171770289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144929983871800025562360385 108697487903850019171770289)
              ·
                refine ⟨81523115927887514378827717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108697487903850019171770289 81523115927887514378827717)
                ·
                  refine ⟨15285584236478908946030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81523115927887514378827717 15285584236478908946030197)
                  ·
                    refine ⟨1433023522169897713690331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15285584236478908946030197 1433023522169897713690331)
                    ·
                      rfl

theorem cell23_8372410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_8372410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372410 prefixEnd_8372410 := by exact prefixLift 8372410
  have htrace : WordTrace (prefixWord ++ tailWord_8372410) baseStart_8372410 baseEnd_8372410 := by
    simpa [prefixWord, tailWord_8372410, baseEnd_8372410] using wordTrace_append hprefix tailTrace_8372410
  have hstable : (prefixWord ++ tailWord_8372410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372410).length < 2 ^ (prefixWord ++ tailWord_8372410).sum := by decide
  have hdescent : baseEnd_8372410 < baseStart_8372410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372460 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_8372460 : Nat := 118140960795 + 8372460 * 2 ^ 59
def prefixEnd_8372460 : Nat := 4983230072969 + 3 ^ 40 * 8372460 * 2
def baseEnd_8372460 : Nat := 4299096240542417945445763

theorem tailTrace_8372460 : CollatzResearch.WordTrace tailWord_8372460 prefixEnd_8372460 4299096240542417945445763 := by
  unfold tailWord_8372460
  simp only [CollatzResearch.WordTrace]
  refine ⟨152684351624007398586385417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203579135498676531448513889 152684351624007398586385417)
  ·
    refine ⟨114513263718005548939789063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152684351624007398586385417 114513263718005548939789063)
    ·
      refine ⟨171769895577008323409683595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114513263718005548939789063 171769895577008323409683595)
      ·
        refine ⟨257654843365512485114525393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171769895577008323409683595 257654843365512485114525393)
        ·
          refine ⟨193241132524134363835894045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257654843365512485114525393 193241132524134363835894045)
          ·
            refine ⟨72465424696550386438460267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193241132524134363835894045 72465424696550386438460267)
            ·
              refine ⟨108698137044825579657690401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72465424696550386438460267 108698137044825579657690401)
              ·
                refine ⟨81523602783619184743267801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108698137044825579657690401 81523602783619184743267801)
                ·
                  refine ⟨61142702087714388557450851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81523602783619184743267801 61142702087714388557450851)
                  ·
                    refine ⟨91714053131571582836176277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61142702087714388557450851 91714053131571582836176277)
                    ·
                      refine ⟨4299096240542417945445763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91714053131571582836176277 4299096240542417945445763)
                      ·
                        rfl

theorem cell23_8372460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_8372460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372460 prefixEnd_8372460 := by exact prefixLift 8372460
  have htrace : WordTrace (prefixWord ++ tailWord_8372460) baseStart_8372460 baseEnd_8372460 := by
    simpa [prefixWord, tailWord_8372460, baseEnd_8372460] using wordTrace_append hprefix tailTrace_8372460
  have hstable : (prefixWord ++ tailWord_8372460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372460).length < 2 ^ (prefixWord ++ tailWord_8372460).sum := by decide
  have hdescent : baseEnd_8372460 < baseStart_8372460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372547 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 6, 4]
def baseStart_8372547 : Nat := 118140960795 + 8372547 * 2 ^ 59
def prefixEnd_8372547 : Nat := 4983230072969 + 3 ^ 40 * 8372547 * 2
def baseEnd_8372547 : Nat := 1433046971119786368352621

theorem tailTrace_8372547 : CollatzResearch.WordTrace tailWord_8372547 prefixEnd_8372547 1433046971119786368352621 := by
  unfold tailWord_8372547
  simp only [CollatzResearch.WordTrace]
  refine ⟨305371876398699611031187895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203581250932466407354125263 305371876398699611031187895)
  ·
    refine ⟨458057814598049416546781843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305371876398699611031187895 458057814598049416546781843)
    ·
      refine ⟨687086721897074124820172765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458057814598049416546781843 687086721897074124820172765)
      ·
        refine ⟨257657520711402796807564787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687086721897074124820172765 257657520711402796807564787)
        ·
          refine ⟨386486281067104195211347181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257657520711402796807564787 386486281067104195211347181)
          ·
            refine ⟨144932355400164073204255193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386486281067104195211347181 144932355400164073204255193)
            ·
              refine ⟨108699266550123054903191395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144932355400164073204255193 108699266550123054903191395)
              ·
                refine ⟨163048899825184582354787093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108699266550123054903191395 163048899825184582354787093)
                ·
                  refine ⟨7642917179305527297880645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163048899825184582354787093 7642917179305527297880645)
                  ·
                    refine ⟨1433046971119786368352621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7642917179305527297880645 1433046971119786368352621)
                    ·
                      rfl

theorem cell23_8372547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 4].length) (baseStart_8372547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372547 prefixEnd_8372547 := by exact prefixLift 8372547
  have htrace : WordTrace (prefixWord ++ tailWord_8372547) baseStart_8372547 baseEnd_8372547 := by
    simpa [prefixWord, tailWord_8372547, baseEnd_8372547] using wordTrace_append hprefix tailTrace_8372547
  have hstable : (prefixWord ++ tailWord_8372547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372547).length < 2 ^ (prefixWord ++ tailWord_8372547).sum := by decide
  have hdescent : baseEnd_8372547 < baseStart_8372547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372560 : List Nat := [2, 1, 1, 1, 1, 17]
def baseStart_8372560 : Nat := 118140960795 + 8372560 * 2 ^ 59
def prefixEnd_8372560 : Nat := 4983230072969 + 3 ^ 40 * 8372560 * 2
def baseEnd_8372560 : Nat := 17691965385217561951421

theorem tailTrace_8372560 : CollatzResearch.WordTrace tailWord_8372560 prefixEnd_8372560 17691965385217561951421 := by
  unfold tailWord_8372560
  simp only [CollatzResearch.WordTrace]
  refine ⟨152686175273826257125705567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203581567031768342834274089 152686175273826257125705567)
  ·
    refine ⟨229029262910739385688558351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152686175273826257125705567 229029262910739385688558351)
    ·
      refine ⟨343543894366109078532837527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229029262910739385688558351 343543894366109078532837527)
      ·
        refine ⟨515315841549163617799256291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343543894366109078532837527 515315841549163617799256291)
        ·
          refine ⟨772973762323745426698884437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515315841549163617799256291 772973762323745426698884437)
          ·
            refine ⟨17691965385217561951421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 17 772973762323745426698884437 17691965385217561951421)
            ·
              rfl

theorem cell23_8372560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 17].length) (baseStart_8372560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372560 prefixEnd_8372560 := by exact prefixLift 8372560
  have htrace : WordTrace (prefixWord ++ tailWord_8372560) baseStart_8372560 baseEnd_8372560 := by
    simpa [prefixWord, tailWord_8372560, baseEnd_8372560] using wordTrace_append hprefix tailTrace_8372560
  have hstable : (prefixWord ++ tailWord_8372560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372560).length < 2 ^ (prefixWord ++ tailWord_8372560).sum := by decide
  have hdescent : baseEnd_8372560 < baseStart_8372560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372567 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_8372567 : Nat := 118140960795 + 8372567 * 2 ^ 59
def prefixEnd_8372567 : Nat := 4983230072969 + 3 ^ 40 * 8372567 * 2
def baseEnd_8372567 : Nat := 4299151182972449026807771

theorem tailTrace_8372567 : CollatzResearch.WordTrace tailWord_8372567 prefixEnd_8372567 4299151182972449026807771 := by
  unfold tailWord_8372567
  simp only [CollatzResearch.WordTrace]
  refine ⟨305372605858627154446915955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203581737239084769631277303 305372605858627154446915955)
  ·
    refine ⟨458058908787940731670373933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305372605858627154446915955 458058908787940731670373933)
    ·
      refine ⟨171772090795477774376390225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458058908787940731670373933 171772090795477774376390225)
      ·
        refine ⟨128829068096608330782292669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171772090795477774376390225 128829068096608330782292669)
        ·
          refine ⟨48310900536228124043359751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128829068096608330782292669 48310900536228124043359751)
          ·
            refine ⟨72466350804342186065039627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48310900536228124043359751 72466350804342186065039627)
            ·
              refine ⟨108699526206513279097559441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72466350804342186065039627 108699526206513279097559441)
              ·
                refine ⟨81524644654884959323169581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108699526206513279097559441 81524644654884959323169581)
                ·
                  refine ⟨30571741745581859746188593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81524644654884959323169581 30571741745581859746188593)
                  ·
                    refine ⟨22928806309186394809641445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30571741745581859746188593 22928806309186394809641445)
                    ·
                      refine ⟨4299151182972449026807771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22928806309186394809641445 4299151182972449026807771)
                      ·
                        rfl

theorem cell23_8372567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_8372567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372567 prefixEnd_8372567 := by exact prefixLift 8372567
  have htrace : WordTrace (prefixWord ++ tailWord_8372567) baseStart_8372567 baseEnd_8372567 := by
    simpa [prefixWord, tailWord_8372567, baseEnd_8372567] using wordTrace_append hprefix tailTrace_8372567
  have hstable : (prefixWord ++ tailWord_8372567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372567).length < 2 ^ (prefixWord ++ tailWord_8372567).sum := by decide
  have hdescent : baseEnd_8372567 < baseStart_8372567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372584 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_8372584 : Nat := 118140960795 + 8372584 * 2 ^ 59
def prefixEnd_8372584 : Nat := 4983230072969 + 3 ^ 40 * 8372584 * 2
def baseEnd_8372584 : Nat := 4299159912143575460295193

theorem tailTrace_8372584 : CollatzResearch.WordTrace tailWord_8372584 prefixEnd_8372584 4299159912143575460295193 := by
  unfold tailWord_8372584
  simp only [CollatzResearch.WordTrace]
  refine ⟨152686612949782783175142403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203582150599710377566856537 152686612949782783175142403)
  ·
    refine ⟨229029919424674174762713605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152686612949782783175142403 229029919424674174762713605)
    ·
      refine ⟨42943109892126407768008801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229029919424674174762713605 42943109892126407768008801)
      ·
        refine ⟨32207332419094805826006601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42943109892126407768008801 32207332419094805826006601)
        ·
          refine ⟨24155499314321104369504951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32207332419094805826006601 24155499314321104369504951)
          ·
            refine ⟨36233248971481656554257427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24155499314321104369504951 36233248971481656554257427)
            ·
              refine ⟨54349873457222484831386141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36233248971481656554257427 54349873457222484831386141)
              ·
                refine ⟨20381202546458431811769803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54349873457222484831386141 20381202546458431811769803)
                ·
                  refine ⟨30571803819687647717654705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20381202546458431811769803 30571803819687647717654705)
                  ·
                    refine ⟨22928852864765735788241029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30571803819687647717654705 22928852864765735788241029)
                    ·
                      refine ⟨4299159912143575460295193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22928852864765735788241029 4299159912143575460295193)
                      ·
                        rfl

theorem cell23_8372584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_8372584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372584 prefixEnd_8372584 := by exact prefixLift 8372584
  have htrace : WordTrace (prefixWord ++ tailWord_8372584) baseStart_8372584 baseEnd_8372584 := by
    simpa [prefixWord, tailWord_8372584, baseEnd_8372584] using wordTrace_append hprefix tailTrace_8372584
  have hstable : (prefixWord ++ tailWord_8372584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372584).length < 2 ^ (prefixWord ++ tailWord_8372584).sum := by decide
  have hdescent : baseEnd_8372584 < baseStart_8372584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372587 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3]
def baseStart_8372587 : Nat := 118140960795 + 8372587 * 2 ^ 59
def prefixEnd_8372587 : Nat := 4983230072969 + 3 ^ 40 * 8372587 * 2
def baseEnd_8372587 : Nat := 4299161452585538948557679

theorem tailTrace_8372587 : CollatzResearch.WordTrace tailWord_8372587 prefixEnd_8372587 4299161452585538948557679 := by
  unfold tailWord_8372587
  simp only [CollatzResearch.WordTrace]
  refine ⟨305373335318554697862644015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203582223545703131908429343 305373335318554697862644015)
  ·
    refine ⟨458060002977832046793966023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305373335318554697862644015 458060002977832046793966023)
    ·
      refine ⟨687090004466748070190949035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458060002977832046793966023 687090004466748070190949035)
      ·
        refine ⟨1030635006700122105286423553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687090004466748070190949035 1030635006700122105286423553)
        ·
          refine ⟨772976255025091578964817665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030635006700122105286423553 772976255025091578964817665)
          ·
            refine ⟨579732191268818684223613249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772976255025091578964817665 579732191268818684223613249)
            ·
              refine ⟨434799143451614013167709937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579732191268818684223613249 434799143451614013167709937)
              ·
                refine ⟨326099357588710509875782453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434799143451614013167709937 326099357588710509875782453)
                ·
                  refine ⟨30571814773941610300854605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326099357588710509875782453 30571814773941610300854605)
                  ·
                    refine ⟨11464430540228103862820477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30571814773941610300854605 11464430540228103862820477)
                    ·
                      refine ⟨4299161452585538948557679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464430540228103862820477 4299161452585538948557679)
                      ·
                        rfl

theorem cell23_8372587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 3].length) (baseStart_8372587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372587 prefixEnd_8372587 := by exact prefixLift 8372587
  have htrace : WordTrace (prefixWord ++ tailWord_8372587) baseStart_8372587 baseEnd_8372587 := by
    simpa [prefixWord, tailWord_8372587, baseEnd_8372587] using wordTrace_append hprefix tailTrace_8372587
  have hstable : (prefixWord ++ tailWord_8372587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372587).length < 2 ^ (prefixWord ++ tailWord_8372587).sum := by decide
  have hdescent : baseEnd_8372587 < baseStart_8372587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372588 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_8372588 : Nat := 118140960795 + 8372588 * 2 ^ 59
def prefixEnd_8372588 : Nat := 4983230072969 + 3 ^ 40 * 8372588 * 2
def baseEnd_8372588 : Nat := 4299161966066193444645175

theorem tailTrace_8372588 : CollatzResearch.WordTrace tailWord_8372588 prefixEnd_8372588 4299161966066193444645175 := by
  unfold tailWord_8372588
  simp only [CollatzResearch.WordTrace]
  refine ⟨152686685895775537516715209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203582247861034050022286945 152686685895775537516715209)
  ·
    refine ⟨114515014421831653137536407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152686685895775537516715209 114515014421831653137536407)
    ·
      refine ⟨171772521632747479706304611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114515014421831653137536407 171772521632747479706304611)
      ·
        refine ⟨257658782449121219559456917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171772521632747479706304611 257658782449121219559456917)
        ·
          refine ⟨12077755427302557166849543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 257658782449121219559456917 12077755427302557166849543)
          ·
            refine ⟨18116633140953835750274315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077755427302557166849543 18116633140953835750274315)
            ·
              refine ⟨27174949711430753625411473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18116633140953835750274315 27174949711430753625411473)
              ·
                refine ⟨20381212283573065219058605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27174949711430753625411473 20381212283573065219058605)
                ·
                  refine ⟨7642954606339899457146977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20381212283573065219058605 7642954606339899457146977)
                  ·
                    refine ⟨5732215954754924592860233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7642954606339899457146977 5732215954754924592860233)
                    ·
                      refine ⟨4299161966066193444645175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732215954754924592860233 4299161966066193444645175)
                      ·
                        rfl

theorem cell23_8372588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_8372588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372588 prefixEnd_8372588 := by exact prefixLift 8372588
  have htrace : WordTrace (prefixWord ++ tailWord_8372588) baseStart_8372588 baseEnd_8372588 := by
    simpa [prefixWord, tailWord_8372588, baseEnd_8372588] using wordTrace_append hprefix tailTrace_8372588
  have hstable : (prefixWord ++ tailWord_8372588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372588).length < 2 ^ (prefixWord ++ tailWord_8372588).sum := by decide
  have hdescent : baseEnd_8372588 < baseStart_8372588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372594 : List Nat := [3, 2, 1, 2, 1, 4, 3, 7]
def baseStart_8372594 : Nat := 118140960795 + 8372594 * 2 ^ 59
def prefixEnd_8372594 : Nat := 4983230072969 + 3 ^ 40 * 8372594 * 2
def baseEnd_8372594 : Nat := 159228335072226682265561

theorem tailTrace_8372594 : CollatzResearch.WordTrace tailWord_8372594 prefixEnd_8372594 159228335072226682265561 := by
  unfold tailWord_8372594
  simp only [CollatzResearch.WordTrace]
  refine ⟨76343397657382334514537209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203582393753019558705432557 76343397657382334514537209)
  ·
    refine ⟨57257548243036750885902907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76343397657382334514537209 57257548243036750885902907)
    ·
      refine ⟨85886322364555126328854361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57257548243036750885902907 85886322364555126328854361)
      ·
        refine ⟨64414741773416344746640771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85886322364555126328854361 64414741773416344746640771)
        ·
          refine ⟨96622112660124517119961157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64414741773416344746640771 96622112660124517119961157)
          ·
            refine ⟨18116646123773346959992717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96622112660124517119961157 18116646123773346959992717)
            ·
              refine ⟨6793742296415005109997269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18116646123773346959992717 6793742296415005109997269)
              ·
                refine ⟨159228335072226682265561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6793742296415005109997269 159228335072226682265561)
                ·
                  rfl

theorem cell23_8372594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_8372594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372594 prefixEnd_8372594 := by exact prefixLift 8372594
  have htrace : WordTrace (prefixWord ++ tailWord_8372594) baseStart_8372594 baseEnd_8372594 := by
    simpa [prefixWord, tailWord_8372594, baseEnd_8372594] using wordTrace_append hprefix tailTrace_8372594
  have hstable : (prefixWord ++ tailWord_8372594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372594).length < 2 ^ (prefixWord ++ tailWord_8372594).sum := by decide
  have hdescent : baseEnd_8372594 < baseStart_8372594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372605 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_8372605 : Nat := 118140960795 + 8372605 * 2 ^ 59
def prefixEnd_8372605 : Nat := 4983230072969 + 3 ^ 40 * 8372605 * 2
def baseEnd_8372605 : Nat := 4299170695237319878132597

theorem tailTrace_8372605 : CollatzResearch.WordTrace tailWord_8372605 prefixEnd_8372605 4299170695237319878132597 := by
  unfold tailWord_8372605
  simp only [CollatzResearch.WordTrace]
  refine ⟨305373991832489486936799269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203582661221659657957866179 305373991832489486936799269)
  ·
    refine ⟨57257623468591778800649863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305373991832489486936799269 57257623468591778800649863)
    ·
      refine ⟨85886435202887668200974795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57257623468591778800649863 85886435202887668200974795)
      ·
        refine ⟨128829652804331502301462193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85886435202887668200974795 128829652804331502301462193)
        ·
          refine ⟨96622239603248626726096645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128829652804331502301462193 96622239603248626726096645)
          ·
            refine ⟨18116669925609117511143121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96622239603248626726096645 18116669925609117511143121)
            ·
              refine ⟨13587502444206838133357341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18116669925609117511143121 13587502444206838133357341)
              ·
                refine ⟨5095313416577564300009003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13587502444206838133357341 5095313416577564300009003)
                ·
                  refine ⟨7642970124866346450013505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095313416577564300009003 7642970124866346450013505)
                  ·
                    refine ⟨5732227593649759837510129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7642970124866346450013505 5732227593649759837510129)
                    ·
                      refine ⟨4299170695237319878132597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732227593649759837510129 4299170695237319878132597)
                      ·
                        rfl

theorem cell23_8372605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_8372605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372605 prefixEnd_8372605 := by exact prefixLift 8372605
  have htrace : WordTrace (prefixWord ++ tailWord_8372605) baseStart_8372605 baseEnd_8372605 := by
    simpa [prefixWord, tailWord_8372605, baseEnd_8372605] using wordTrace_append hprefix tailTrace_8372605
  have hstable : (prefixWord ++ tailWord_8372605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372605).length < 2 ^ (prefixWord ++ tailWord_8372605).sum := by decide
  have hdescent : baseEnd_8372605 < baseStart_8372605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372638 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_8372638 : Nat := 118140960795 + 8372638 * 2 ^ 59
def prefixEnd_8372638 : Nat := 4983230072969 + 3 ^ 40 * 8372638 * 2
def baseEnd_8372638 : Nat := 4299187640098918249019945

theorem tailTrace_8372638 : CollatzResearch.WordTrace tailWord_8372638 prefixEnd_8372638 4299187640098918249019945 := by
  unfold tailWord_8372638
  simp only [CollatzResearch.WordTrace]
  refine ⟨38171899430171241696593821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203583463627579955715167045 38171899430171241696593821)
  ·
    refine ⟨14314462286314215636222683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38171899430171241696593821 14314462286314215636222683)
    ·
      refine ⟨21471693429471323454334025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14314462286314215636222683 21471693429471323454334025)
      ·
        refine ⟨16103770072103492590750519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21471693429471323454334025 16103770072103492590750519)
        ·
          refine ⟨24155655108155238886125779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16103770072103492590750519 24155655108155238886125779)
          ·
            refine ⟨36233482662232858329188669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24155655108155238886125779 36233482662232858329188669)
            ·
              refine ⟨13587555998337321873445751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36233482662232858329188669 13587555998337321873445751)
              ·
                refine ⟨20381333997505982810168627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13587555998337321873445751 20381333997505982810168627)
                ·
                  refine ⟨30572000996258974215252941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20381333997505982810168627 30572000996258974215252941)
                  ·
                    refine ⟨11464500373597115330719853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30572000996258974215252941 11464500373597115330719853)
                    ·
                      refine ⟨4299187640098918249019945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464500373597115330719853 4299187640098918249019945)
                      ·
                        rfl

theorem cell23_8372638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_8372638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372638 prefixEnd_8372638 := by exact prefixLift 8372638
  have htrace : WordTrace (prefixWord ++ tailWord_8372638) baseStart_8372638 baseEnd_8372638 := by
    simpa [prefixWord, tailWord_8372638, baseEnd_8372638] using wordTrace_append hprefix tailTrace_8372638
  have hstable : (prefixWord ++ tailWord_8372638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372638).length < 2 ^ (prefixWord ++ tailWord_8372638).sum := by decide
  have hdescent : baseEnd_8372638 < baseStart_8372638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372727 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 8]
def baseStart_8372727 : Nat := 118140960795 + 8372727 * 2 ^ 59
def prefixEnd_8372727 : Nat := 4983230072969 + 3 ^ 40 * 8372727 * 2
def baseEnd_8372727 : Nat := 1433077779959056133602345

theorem tailTrace_8372727 : CollatzResearch.WordTrace tailWord_8372727 prefixEnd_8372727 1433077779959056133602345 := by
  unfold tailWord_8372727
  simp only [CollatzResearch.WordTrace]
  refine ⟨305378441538047501772740435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203585627692031667848493623 305378441538047501772740435)
  ·
    refine ⟨458067662307071252659110653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305378441538047501772740435 458067662307071252659110653)
    ·
      refine ⟨171775373365151719747166495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458067662307071252659110653 171775373365151719747166495)
      ·
        refine ⟨257663060047727579620749743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171775373365151719747166495 257663060047727579620749743)
        ·
          refine ⟨386494590071591369431124615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257663060047727579620749743 386494590071591369431124615)
          ·
            refine ⟨579741885107387054146686923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386494590071591369431124615 579741885107387054146686923)
            ·
              refine ⟨869612827661080581220030385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579741885107387054146686923 869612827661080581220030385)
              ·
                refine ⟨652209620745810435915022789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869612827661080581220030385 652209620745810435915022789)
                ·
                  refine ⟨122289303889839456734066773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652209620745810435915022789 122289303889839456734066773)
                  ·
                    refine ⟨1433077779959056133602345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122289303889839456734066773 1433077779959056133602345)
                    ·
                      rfl

theorem cell23_8372727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_8372727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372727 prefixEnd_8372727 := by exact prefixLift 8372727
  have htrace : WordTrace (prefixWord ++ tailWord_8372727) baseStart_8372727 baseEnd_8372727 := by
    simpa [prefixWord, tailWord_8372727, baseEnd_8372727] using wordTrace_append hprefix tailTrace_8372727
  have hstable : (prefixWord ++ tailWord_8372727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372727).length < 2 ^ (prefixWord ++ tailWord_8372727).sum := by decide
  have hdescent : baseEnd_8372727 < baseStart_8372727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372771 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3]
def baseStart_8372771 : Nat := 118140960795 + 8372771 * 2 ^ 59
def prefixEnd_8372771 : Nat := 4983230072969 + 3 ^ 40 * 8372771 * 2
def baseEnd_8372771 : Nat := 4299255933025966228656833

theorem tailTrace_8372771 : CollatzResearch.WordTrace tailWord_8372771 prefixEnd_8372771 4299255933025966228656833 := by
  unfold tailWord_8372771
  simp only [CollatzResearch.WordTrace]
  refine ⟨305380046349888097287342167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203586697566592064858228111 305380046349888097287342167)
  ·
    refine ⟨458070069524832145931013251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305380046349888097287342167 458070069524832145931013251)
    ·
      refine ⟨687105104287248218896519877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458070069524832145931013251 687105104287248218896519877)
      ·
        refine ⟨128832207053859041043097477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687105104287248218896519877 128832207053859041043097477)
        ·
          refine ⟨24156038822598570195580777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128832207053859041043097477 24156038822598570195580777)
          ·
            refine ⟨18117029116948927646685583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156038822598570195580777 18117029116948927646685583)
            ·
              refine ⟨27175543675423391470028375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117029116948927646685583 27175543675423391470028375)
              ·
                refine ⟨40763315513135087205042563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27175543675423391470028375 40763315513135087205042563)
                ·
                  refine ⟨61144973269702630807563845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40763315513135087205042563 61144973269702630807563845)
                  ·
                    refine ⟨11464682488069243276418221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61144973269702630807563845 11464682488069243276418221)
                    ·
                      refine ⟨4299255933025966228656833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464682488069243276418221 4299255933025966228656833)
                      ·
                        rfl

theorem cell23_8372771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_8372771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372771 prefixEnd_8372771 := by exact prefixLift 8372771
  have htrace : WordTrace (prefixWord ++ tailWord_8372771) baseStart_8372771 baseEnd_8372771 := by
    simpa [prefixWord, tailWord_8372771, baseEnd_8372771] using wordTrace_append hprefix tailTrace_8372771
  have hstable : (prefixWord ++ tailWord_8372771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372771).length < 2 ^ (prefixWord ++ tailWord_8372771).sum := by decide
  have hdescent : baseEnd_8372771 < baseStart_8372771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372794 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_8372794 : Nat := 118140960795 + 8372794 * 2 ^ 59
def prefixEnd_8372794 : Nat := 4983230072969 + 3 ^ 40 * 8372794 * 2
def baseEnd_8372794 : Nat := 4299267743081019638669227

theorem tailTrace_8372794 : CollatzResearch.WordTrace tailWord_8372794 prefixEnd_8372794 4299267743081019638669227 := by
  unfold tailWord_8372794
  simp only [CollatzResearch.WordTrace]
  refine ⟨76345221307201193053857359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203587256819203181476952957 76345221307201193053857359)
  ·
    refine ⟨114517831960801789580786039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76345221307201193053857359 114517831960801789580786039)
    ·
      refine ⟨171776747941202684371179059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114517831960801789580786039 171776747941202684371179059)
      ·
        refine ⟨257665121911804026556768589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171776747941202684371179059 257665121911804026556768589)
        ·
          refine ⟨96624420716926509958788221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257665121911804026556768589 96624420716926509958788221)
          ·
            refine ⟨36234157768847441234545583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96624420716926509958788221 36234157768847441234545583)
            ·
              refine ⟨54351236653271161851818375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36234157768847441234545583 54351236653271161851818375)
              ·
                refine ⟨81526854979906742777727563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54351236653271161851818375 81526854979906742777727563)
                ·
                  refine ⟨122290282469860114166591345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81526854979906742777727563 122290282469860114166591345)
                  ·
                    refine ⟨91717711852395085624943509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122290282469860114166591345 91717711852395085624943509)
                    ·
                      refine ⟨4299267743081019638669227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91717711852395085624943509 4299267743081019638669227)
                      ·
                        rfl

theorem cell23_8372794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_8372794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372794 prefixEnd_8372794 := by exact prefixLift 8372794
  have htrace : WordTrace (prefixWord ++ tailWord_8372794) baseStart_8372794 baseEnd_8372794 := by
    simpa [prefixWord, tailWord_8372794, baseEnd_8372794] using wordTrace_append hprefix tailTrace_8372794
  have hstable : (prefixWord ++ tailWord_8372794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372794).length < 2 ^ (prefixWord ++ tailWord_8372794).sum := by decide
  have hdescent : baseEnd_8372794 < baseStart_8372794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372811 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 5, 2]
def baseStart_8372811 : Nat := 118140960795 + 8372811 * 2 ^ 59
def prefixEnd_8372811 : Nat := 4983230072969 + 3 ^ 40 * 8372811 * 2
def baseEnd_8372811 : Nat := 4299276472252146072156649

theorem tailTrace_8372811 : CollatzResearch.WordTrace tailWord_8372811 prefixEnd_8372811 4299276472252146072156649 := by
  unfold tailWord_8372811
  simp only [CollatzResearch.WordTrace]
  refine ⟨305381505269743184118798287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203587670179828789412532191 305381505269743184118798287)
  ·
    refine ⟨458072257904614776178197431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305381505269743184118798287 458072257904614776178197431)
    ·
      refine ⟨687108386856922164267296147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458072257904614776178197431 687108386856922164267296147)
      ·
        refine ⟨1030662580285383246400944221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687108386856922164267296147 1030662580285383246400944221)
        ·
          refine ⟨386498467607018717400354083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1030662580285383246400944221 386498467607018717400354083)
          ·
            refine ⟨579747701410528076100531125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386498467607018717400354083 579747701410528076100531125)
            ·
              refine ⟨54351347007237007134424793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 579747701410528076100531125 54351347007237007134424793)
              ·
                refine ⟨40763510255427755350818595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54351347007237007134424793 40763510255427755350818595)
                ·
                  refine ⟨61145265383141633026227893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40763510255427755350818595 61145265383141633026227893)
                  ·
                    refine ⟨5732368629669528096208865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61145265383141633026227893 5732368629669528096208865)
                    ·
                      refine ⟨4299276472252146072156649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732368629669528096208865 4299276472252146072156649)
                      ·
                        rfl

theorem cell23_8372811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5, 2].length) (baseStart_8372811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372811 prefixEnd_8372811 := by exact prefixLift 8372811
  have htrace : WordTrace (prefixWord ++ tailWord_8372811) baseStart_8372811 baseEnd_8372811 := by
    simpa [prefixWord, tailWord_8372811, baseEnd_8372811] using wordTrace_append hprefix tailTrace_8372811
  have hstable : (prefixWord ++ tailWord_8372811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372811).length < 2 ^ (prefixWord ++ tailWord_8372811).sum := by decide
  have hdescent : baseEnd_8372811 < baseStart_8372811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372814 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_8372814 : Nat := 118140960795 + 8372814 * 2 ^ 59
def prefixEnd_8372814 : Nat := 4983230072969 + 3 ^ 40 * 8372814 * 2
def baseEnd_8372814 : Nat := 4299278012694109560419135

theorem tailTrace_8372814 : CollatzResearch.WordTrace tailWord_8372814 prefixEnd_8372814 4299278012694109560419135 := by
  unfold tailWord_8372814
  simp only [CollatzResearch.WordTrace]
  refine ⟨38172701836091539453894687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203587743125821543754104997 38172701836091539453894687)
  ·
    refine ⟨57259052754137309180842031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38172701836091539453894687 57259052754137309180842031)
    ·
      refine ⟨85888579131205963771263047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57259052754137309180842031 85888579131205963771263047)
      ·
        refine ⟨128832868696808945656894571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85888579131205963771263047 128832868696808945656894571)
        ·
          refine ⟨193249303045213418485341857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128832868696808945656894571 193249303045213418485341857)
          ·
            refine ⟨144936977283910063864006393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193249303045213418485341857 144936977283910063864006393)
            ·
              refine ⟨108702732962932547898004795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144936977283910063864006393 108702732962932547898004795)
              ·
                refine ⟨163054099444398821847007193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108702732962932547898004795 163054099444398821847007193)
                ·
                  refine ⟨122290574583299116385255395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163054099444398821847007193 122290574583299116385255395)
                  ·
                    refine ⟨183435861874948674577883093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122290574583299116385255395 183435861874948674577883093)
                    ·
                      refine ⟨4299278012694109560419135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183435861874948674577883093 4299278012694109560419135)
                      ·
                        rfl

theorem cell23_8372814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_8372814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372814 prefixEnd_8372814 := by exact prefixLift 8372814
  have htrace : WordTrace (prefixWord ++ tailWord_8372814) baseStart_8372814 baseEnd_8372814 := by
    simpa [prefixWord, tailWord_8372814, baseEnd_8372814] using wordTrace_append hprefix tailTrace_8372814
  have hstable : (prefixWord ++ tailWord_8372814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372814).length < 2 ^ (prefixWord ++ tailWord_8372814).sum := by decide
  have hdescent : baseEnd_8372814 < baseStart_8372814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372818 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_8372818 : Nat := 118140960795 + 8372818 * 2 ^ 59
def prefixEnd_8372818 : Nat := 4983230072969 + 3 ^ 40 * 8372818 * 2
def baseEnd_8372818 : Nat := 4299280066616727544769117

theorem tailTrace_8372818 : CollatzResearch.WordTrace tailWord_8372818 prefixEnd_8372818 4299280066616727544769117 := by
  unfold tailWord_8372818
  simp only [CollatzResearch.WordTrace]
  refine ⟨76345440145179456078575777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203587840387145216209535405 76345440145179456078575777)
  ·
    refine ⟨57259080108884592058931833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76345440145179456078575777 57259080108884592058931833)
    ·
      refine ⟨42944310081663444044198875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57259080108884592058931833 42944310081663444044198875)
      ·
        refine ⟨64416465122495166066298313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42944310081663444044198875 64416465122495166066298313)
        ·
          refine ⟨48312348841871374549723735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64416465122495166066298313 48312348841871374549723735)
          ·
            refine ⟨72468523262807061824585603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48312348841871374549723735 72468523262807061824585603)
            ·
              refine ⟨108702784894210592736878405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72468523262807061824585603 108702784894210592736878405)
              ·
                refine ⟨20381772167664486138164701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108702784894210592736878405 20381772167664486138164701)
                ·
                  refine ⟨7643164562874182301811763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20381772167664486138164701 7643164562874182301811763)
                  ·
                    refine ⟨11464746844311273452717645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7643164562874182301811763 11464746844311273452717645)
                    ·
                      refine ⟨4299280066616727544769117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464746844311273452717645 4299280066616727544769117)
                      ·
                        rfl

theorem cell23_8372818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_8372818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372818 prefixEnd_8372818 := by exact prefixLift 8372818
  have htrace : WordTrace (prefixWord ++ tailWord_8372818) baseStart_8372818 baseEnd_8372818 := by
    simpa [prefixWord, tailWord_8372818, baseEnd_8372818] using wordTrace_append hprefix tailTrace_8372818
  have hstable : (prefixWord ++ tailWord_8372818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372818).length < 2 ^ (prefixWord ++ tailWord_8372818).sum := by decide
  have hdescent : baseEnd_8372818 < baseStart_8372818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372821 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_8372821 : Nat := 118140960795 + 8372821 * 2 ^ 59
def prefixEnd_8372821 : Nat := 4983230072969 + 3 ^ 40 * 8372821 * 2
def baseEnd_8372821 : Nat := 1433093869019563677677201

theorem tailTrace_8372821 : CollatzResearch.WordTrace tailWord_8372821 prefixEnd_8372821 1433093869019563677677201 := by
  unfold tailWord_8372821
  simp only [CollatzResearch.WordTrace]
  refine ⟨305381869999706955826662317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203587913333137970551108211 305381869999706955826662317)
  ·
    refine ⟨114518201249890108434998369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305381869999706955826662317 114518201249890108434998369)
    ·
      refine ⟨85888650937417581326248777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114518201249890108434998369 85888650937417581326248777)
      ·
        refine ⟨64416488203063185994686583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85888650937417581326248777 64416488203063185994686583)
        ·
          refine ⟨96624732304594778992029875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64416488203063185994686583 96624732304594778992029875)
          ·
            refine ⟨144937098456892168488044813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96624732304594778992029875 144937098456892168488044813)
            ·
              refine ⟨54351411921334563183016805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144937098456892168488044813 54351411921334563183016805)
              ·
                refine ⟨10190889735250230596815651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54351411921334563183016805 10190889735250230596815651)
                ·
                  refine ⟨15286334602875345895223477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10190889735250230596815651 15286334602875345895223477)
                  ·
                    refine ⟨1433093869019563677677201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15286334602875345895223477 1433093869019563677677201)
                    ·
                      rfl

theorem cell23_8372821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_8372821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372821 prefixEnd_8372821 := by exact prefixLift 8372821
  have htrace : WordTrace (prefixWord ++ tailWord_8372821) baseStart_8372821 baseEnd_8372821 := by
    simpa [prefixWord, tailWord_8372821, baseEnd_8372821] using wordTrace_append hprefix tailTrace_8372821
  have hstable : (prefixWord ++ tailWord_8372821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372821).length < 2 ^ (prefixWord ++ tailWord_8372821).sum := by decide
  have hdescent : baseEnd_8372821 < baseStart_8372821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372845 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_8372845 : Nat := 118140960795 + 8372845 * 2 ^ 59
def prefixEnd_8372845 : Nat := 4983230072969 + 3 ^ 40 * 8372845 * 2
def baseEnd_8372845 : Nat := 4299293930594398939131493

theorem tailTrace_8372845 : CollatzResearch.WordTrace tailWord_8372845 prefixEnd_8372845 4299293930594398939131493 := by
  unfold tailWord_8372845
  simp only [CollatzResearch.WordTrace]
  refine ⟨305382745351620007925535989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203588496901080005283690659 305382745351620007925535989)
  ·
    refine ⟨28629632376714375743018999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305382745351620007925535989 28629632376714375743018999)
    ·
      refine ⟨42944448565071563614528499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28629632376714375743018999 42944448565071563614528499)
      ·
        refine ⟨64416672847607345421792749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42944448565071563614528499 64416672847607345421792749)
        ·
          refine ⟨24156252317852754533172281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64416672847607345421792749 24156252317852754533172281)
          ·
            refine ⟨18117189238389565899879211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156252317852754533172281 18117189238389565899879211)
            ·
              refine ⟨27175783857584348849818817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117189238389565899879211 27175783857584348849818817)
              ·
                refine ⟨20381837893188261637364113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27175783857584348849818817 20381837893188261637364113)
                ·
                  refine ⟨15286378419891196228023085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20381837893188261637364113 15286378419891196228023085)
                  ·
                    refine ⟨5732391907459198585508657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15286378419891196228023085 5732391907459198585508657)
                    ·
                      refine ⟨4299293930594398939131493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732391907459198585508657 4299293930594398939131493)
                      ·
                        rfl

theorem cell23_8372845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_8372845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372845 prefixEnd_8372845 := by exact prefixLift 8372845
  have htrace : WordTrace (prefixWord ++ tailWord_8372845) baseStart_8372845 baseEnd_8372845 := by
    simpa [prefixWord, tailWord_8372845, baseEnd_8372845] using wordTrace_append hprefix tailTrace_8372845
  have hstable : (prefixWord ++ tailWord_8372845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372845).length < 2 ^ (prefixWord ++ tailWord_8372845).sum := by decide
  have hdescent : baseEnd_8372845 < baseStart_8372845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372864 : List Nat := [2, 1, 1, 2, 1, 5, 1, 10]
def baseStart_8372864 : Nat := 118140960795 + 8372864 * 2 ^ 59
def prefixEnd_8372864 : Nat := 4983230072969 + 3 ^ 40 * 8372864 * 2
def baseEnd_8372864 : Nat := 159233469878771643140515

theorem tailTrace_8372864 : CollatzResearch.WordTrace tailWord_8372864 prefixEnd_8372864 159233469878771643140515 := by
  unfold tailWord_8372864
  simp only [CollatzResearch.WordTrace]
  refine ⟨152691719169275587085238823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203588958892367449446985097 152691719169275587085238823)
  ·
    refine ⟨229037578753913380627858235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152691719169275587085238823 229037578753913380627858235)
    ·
      refine ⟨343556368130870070941787353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229037578753913380627858235 343556368130870070941787353)
      ·
        refine ⟨257667276098152553206340515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343556368130870070941787353 257667276098152553206340515)
        ·
          refine ⟨386500914147228829809510773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257667276098152553206340515 386500914147228829809510773)
          ·
            refine ⟨36234460701302702794641635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386500914147228829809510773 36234460701302702794641635)
            ·
              refine ⟨54351691051954054191962453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36234460701302702794641635 54351691051954054191962453)
              ·
                refine ⟨159233469878771643140515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54351691051954054191962453 159233469878771643140515)
                ·
                  rfl

theorem cell23_8372864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 10].length) (baseStart_8372864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372864 prefixEnd_8372864 := by exact prefixLift 8372864
  have htrace : WordTrace (prefixWord ++ tailWord_8372864) baseStart_8372864 baseEnd_8372864 := by
    simpa [prefixWord, tailWord_8372864, baseEnd_8372864] using wordTrace_append hprefix tailTrace_8372864
  have hstable : (prefixWord ++ tailWord_8372864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372864).length < 2 ^ (prefixWord ++ tailWord_8372864).sum := by decide
  have hdescent : baseEnd_8372864 < baseStart_8372864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372871 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_8372871 : Nat := 118140960795 + 8372871 * 2 ^ 59
def prefixEnd_8372871 : Nat := 4983230072969 + 3 ^ 40 * 8372871 * 2
def baseEnd_8372871 : Nat := 4299307281091415837406373

theorem tailTrace_8372871 : CollatzResearch.WordTrace tailWord_8372871 prefixEnd_8372871 4299307281091415837406373 := by
  unfold tailWord_8372871
  simp only [CollatzResearch.WordTrace]
  refine ⟨305383693649525814365982467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203589129099683876243988311 305383693649525814365982467)
  ·
    refine ⟨458075540474288721548973701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305383693649525814365982467 458075540474288721548973701)
    ·
      refine ⟨85889163838929135290432569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458075540474288721548973701 85889163838929135290432569)
      ·
        refine ⟨64416872879196851467824427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85889163838929135290432569 64416872879196851467824427)
        ·
          refine ⟨96625309318795277201736641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64416872879196851467824427 96625309318795277201736641)
          ·
            refine ⟨72468981989096457901302481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96625309318795277201736641 72468981989096457901302481)
            ·
              refine ⟨54351736491822343425976861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72468981989096457901302481 54351736491822343425976861)
              ·
                refine ⟨20381901184433378784741323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54351736491822343425976861 20381901184433378784741323)
                ·
                  refine ⟨30572851776650068177111985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20381901184433378784741323 30572851776650068177111985)
                  ·
                    refine ⟨22929638832487551132833989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30572851776650068177111985 22929638832487551132833989)
                    ·
                      refine ⟨4299307281091415837406373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22929638832487551132833989 4299307281091415837406373)
                      ·
                        rfl

theorem cell23_8372871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_8372871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372871 prefixEnd_8372871 := by exact prefixLift 8372871
  have htrace : WordTrace (prefixWord ++ tailWord_8372871) baseStart_8372871 baseEnd_8372871 := by
    simpa [prefixWord, tailWord_8372871, baseEnd_8372871] using wordTrace_append hprefix tailTrace_8372871
  have hstable : (prefixWord ++ tailWord_8372871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372871).length < 2 ^ (prefixWord ++ tailWord_8372871).sum := by decide
  have hdescent : baseEnd_8372871 < baseStart_8372871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372878 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_8372878 : Nat := 118140960795 + 8372878 * 2 ^ 59
def prefixEnd_8372878 : Nat := 4983230072969 + 3 ^ 40 * 8372878 * 2
def baseEnd_8372878 : Nat := 4299310875455997310018841

theorem tailTrace_8372878 : CollatzResearch.WordTrace tailWord_8372878 prefixEnd_8372878 4299310875455997310018841 := by
  unfold tailWord_8372878
  simp only [CollatzResearch.WordTrace]
  refine ⟨38172993620062556820185911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203589299307000303040991525 38172993620062556820185911)
  ·
    refine ⟨57259490430093835230278867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38172993620062556820185911 57259490430093835230278867)
    ·
      refine ⟨85889235645140752845418301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57259490430093835230278867 85889235645140752845418301)
      ·
        refine ⟨32208463366927782317031863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85889235645140752845418301 32208463366927782317031863)
        ·
          refine ⟨48312695050391673475547795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32208463366927782317031863 48312695050391673475547795)
          ·
            refine ⟨72469042575587510213321693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48312695050391673475547795 72469042575587510213321693)
            ·
              refine ⟨27175890965845316329995635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72469042575587510213321693 27175890965845316329995635)
              ·
                refine ⟨40763836448767974494993453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27175890965845316329995635 40763836448767974494993453)
                ·
                  refine ⟨15286438668287990435622545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40763836448767974494993453 15286438668287990435622545)
                  ·
                    refine ⟨11464829001215992826716909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15286438668287990435622545 11464829001215992826716909)
                    ·
                      refine ⟨4299310875455997310018841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464829001215992826716909 4299310875455997310018841)
                      ·
                        rfl

theorem cell23_8372878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_8372878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372878 prefixEnd_8372878 := by exact prefixLift 8372878
  have htrace : WordTrace (prefixWord ++ tailWord_8372878) baseStart_8372878 baseEnd_8372878 := by
    simpa [prefixWord, tailWord_8372878, baseEnd_8372878] using wordTrace_append hprefix tailTrace_8372878
  have hstable : (prefixWord ++ tailWord_8372878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372878).length < 2 ^ (prefixWord ++ tailWord_8372878).sum := by decide
  have hdescent : baseEnd_8372878 < baseStart_8372878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372903 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_8372903 : Nat := 118140960795 + 8372903 * 2 ^ 59
def prefixEnd_8372903 : Nat := 4983230072969 + 3 ^ 40 * 8372903 * 2
def baseEnd_8372903 : Nat := 4299323712472359712206227

theorem tailTrace_8372903 : CollatzResearch.WordTrace tailWord_8372903 prefixEnd_8372903 4299323712472359712206227 := by
  unfold tailWord_8372903
  simp only [CollatzResearch.WordTrace]
  refine ⟨305384860785409883831147363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203589907190273255887431575 305384860785409883831147363)
  ·
    refine ⟨458077291178114825746721045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305384860785409883831147363 458077291178114825746721045)
    ·
      refine ⟨21472373023974132456877549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 458077291178114825746721045 21472373023974132456877549)
      ·
        refine ⟨8052139883990299671329081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21472373023974132456877549 8052139883990299671329081)
        ·
          refine ⟨6039104912992724753496811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8052139883990299671329081 6039104912992724753496811)
          ·
            refine ⟨9058657369489087130245217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039104912992724753496811 9058657369489087130245217)
            ·
              refine ⟨6793993027116815347683913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9058657369489087130245217 6793993027116815347683913)
              ·
                refine ⟨5095494770337611510762935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793993027116815347683913 5095494770337611510762935)
                ·
                  refine ⟨7643242155506417266144403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095494770337611510762935 7643242155506417266144403)
                  ·
                    refine ⟨11464863233259625899216605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7643242155506417266144403 11464863233259625899216605)
                    ·
                      refine ⟨4299323712472359712206227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464863233259625899216605 4299323712472359712206227)
                      ·
                        rfl

theorem cell23_8372903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_8372903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372903 prefixEnd_8372903 := by exact prefixLift 8372903
  have htrace : WordTrace (prefixWord ++ tailWord_8372903) baseStart_8372903 baseEnd_8372903 := by
    simpa [prefixWord, tailWord_8372903, baseEnd_8372903] using wordTrace_append hprefix tailTrace_8372903
  have hstable : (prefixWord ++ tailWord_8372903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372903).length < 2 ^ (prefixWord ++ tailWord_8372903).sum := by decide
  have hdescent : baseEnd_8372903 < baseStart_8372903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372909 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_8372909 : Nat := 118140960795 + 8372909 * 2 ^ 59
def prefixEnd_8372909 : Nat := 4983230072969 + 3 ^ 40 * 8372909 * 2
def baseEnd_8372909 : Nat := 4299326793356286688731199

theorem tailTrace_8372909 : CollatzResearch.WordTrace tailWord_8372909 prefixEnd_8372909 4299326793356286688731199 := by
  unfold tailWord_8372909
  simp only [CollatzResearch.WordTrace]
  refine ⟨305385079623388146855865781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203590053082258764570577187 305385079623388146855865781)
  ·
    refine ⟨28629851214692638767737417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305385079623388146855865781 28629851214692638767737417)
    ·
      refine ⟨21472388411019479075803063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28629851214692638767737417 21472388411019479075803063)
      ·
        refine ⟨32208582616529218613704595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21472388411019479075803063 32208582616529218613704595)
        ·
          refine ⟨48312873924793827920556893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32208582616529218613704595 48312873924793827920556893)
          ·
            refine ⟨18117327721797685470208835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48312873924793827920556893 18117327721797685470208835)
            ·
              refine ⟨27175991582696528205313253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117327721797685470208835 27175991582696528205313253)
              ·
                refine ⟨5095498421755599038496235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27175991582696528205313253 5095498421755599038496235)
                ·
                  refine ⟨7643247632633398557744353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095498421755599038496235 7643247632633398557744353)
                  ·
                    refine ⟨5732435724475048918308265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643247632633398557744353 5732435724475048918308265)
                    ·
                      refine ⟨4299326793356286688731199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732435724475048918308265 4299326793356286688731199)
                      ·
                        rfl

theorem cell23_8372909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_8372909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372909 prefixEnd_8372909 := by exact prefixLift 8372909
  have htrace : WordTrace (prefixWord ++ tailWord_8372909) baseStart_8372909 baseEnd_8372909 := by
    simpa [prefixWord, tailWord_8372909, baseEnd_8372909] using wordTrace_append hprefix tailTrace_8372909
  have hstable : (prefixWord ++ tailWord_8372909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372909).length < 2 ^ (prefixWord ++ tailWord_8372909).sum := by decide
  have hdescent : baseEnd_8372909 < baseStart_8372909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372925 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_8372925 : Nat := 118140960795 + 8372925 * 2 ^ 59
def prefixEnd_8372925 : Nat := 4983230072969 + 3 ^ 40 * 8372925 * 2
def baseEnd_8372925 : Nat := 4299335009046758626131125

theorem tailTrace_8372925 : CollatzResearch.WordTrace tailWord_8372925 prefixEnd_8372925 4299335009046758626131125 := by
  unfold tailWord_8372925
  simp only [CollatzResearch.WordTrace]
  refine ⟨305385663191330181588448229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203590442127553454392298819 305385663191330181588448229)
  ·
    refine ⟨57259811848374409047834043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305385663191330181588448229 57259811848374409047834043)
    ·
      refine ⟨85889717772561613571751065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57259811848374409047834043 85889717772561613571751065)
      ·
        refine ⟨64417288329421210178813299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85889717772561613571751065 64417288329421210178813299)
        ·
          refine ⟨96625932494131815268219949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64417288329421210178813299 96625932494131815268219949)
          ·
            refine ⟨36234724685299430725582481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96625932494131815268219949 36234724685299430725582481)
            ·
              refine ⟨27176043513974573044186861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36234724685299430725582481 27176043513974573044186861)
              ·
                refine ⟨10191016317740464891570073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27176043513974573044186861 10191016317740464891570073)
                ·
                  refine ⟨7643262238305348668677555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10191016317740464891570073 7643262238305348668677555)
                  ·
                    refine ⟨11464893357458023003016333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7643262238305348668677555 11464893357458023003016333)
                    ·
                      refine ⟨4299335009046758626131125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11464893357458023003016333 4299335009046758626131125)
                      ·
                        rfl

theorem cell23_8372925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_8372925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372925 prefixEnd_8372925 := by exact prefixLift 8372925
  have htrace : WordTrace (prefixWord ++ tailWord_8372925) baseStart_8372925 baseEnd_8372925 := by
    simpa [prefixWord, tailWord_8372925, baseEnd_8372925] using wordTrace_append hprefix tailTrace_8372925
  have hstable : (prefixWord ++ tailWord_8372925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372925).length < 2 ^ (prefixWord ++ tailWord_8372925).sum := by decide
  have hdescent : baseEnd_8372925 < baseStart_8372925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372952 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_8372952 : Nat := 118140960795 + 8372952 * 2 ^ 59
def prefixEnd_8372952 : Nat := 4983230072969 + 3 ^ 40 * 8372952 * 2
def baseEnd_8372952 : Nat := 4299348873024430020493501

theorem tailTrace_8372952 : CollatzResearch.WordTrace tailWord_8372952 prefixEnd_8372952 4299348873024430020493501 := by
  unfold tailWord_8372952
  simp only [CollatzResearch.WordTrace]
  refine ⟨152693323981116182599840555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203591098641488243466454073 152693323981116182599840555)
  ·
    refine ⟨229039985971674273899760833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152693323981116182599840555 229039985971674273899760833)
    ·
      refine ⟨171779989478755705424820625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229039985971674273899760833 171779989478755705424820625)
      ·
        refine ⟨128834992109066779068615469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171779989478755705424820625 128834992109066779068615469)
        ·
          refine ⟨48313122040900042150730801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128834992109066779068615469 48313122040900042150730801)
          ·
            refine ⟨36234841530675031613048101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48313122040900042150730801 36234841530675031613048101)
            ·
              refine ⟨6794032787001568427446519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36234841530675031613048101 6794032787001568427446519)
              ·
                refine ⟨10191049180502352641169779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794032787001568427446519 10191049180502352641169779)
                ·
                  refine ⟨15286573770753528961754669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191049180502352641169779 15286573770753528961754669)
                  ·
                    refine ⟨5732465164032573360658001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15286573770753528961754669 5732465164032573360658001)
                    ·
                      refine ⟨4299348873024430020493501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732465164032573360658001 4299348873024430020493501)
                      ·
                        rfl

theorem cell23_8372952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_8372952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372952 prefixEnd_8372952 := by exact prefixLift 8372952
  have htrace : WordTrace (prefixWord ++ tailWord_8372952) baseStart_8372952 baseEnd_8372952 := by
    simpa [prefixWord, tailWord_8372952, baseEnd_8372952] using wordTrace_append hprefix tailTrace_8372952
  have hstable : (prefixWord ++ tailWord_8372952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372952).length < 2 ^ (prefixWord ++ tailWord_8372952).sum := by decide
  have hdescent : baseEnd_8372952 < baseStart_8372952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8372978 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_8372978 : Nat := 118140960795 + 8372978 * 2 ^ 59
def prefixEnd_8372978 : Nat := 4983230072969 + 3 ^ 40 * 8372978 * 2
def baseEnd_8372978 : Nat := 4299362223521446918768381

theorem tailTrace_8372978 : CollatzResearch.WordTrace tailWord_8372978 prefixEnd_8372978 4299362223521446918768381 := by
  unfold tailWord_8372978
  simp only [CollatzResearch.WordTrace]
  refine ⟨76346899065034542910031897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203591730840092114426751725 76346899065034542910031897)
  ·
    refine ⟨57260174298775907182523923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76346899065034542910031897 57260174298775907182523923)
    ·
      refine ⟨85890261448163860773785885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57260174298775907182523923 85890261448163860773785885)
      ·
        refine ⟨32208848043061447790169707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85890261448163860773785885 32208848043061447790169707)
        ·
          refine ⟨48313272064592171685254561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32208848043061447790169707 48313272064592171685254561)
          ·
            refine ⟨36234954048444128763940921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48313272064592171685254561 36234954048444128763940921)
            ·
              refine ⟨27176215536333096572955691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36234954048444128763940921 27176215536333096572955691)
              ·
                refine ⟨40764323304499644859433537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27176215536333096572955691 40764323304499644859433537)
                ·
                  refine ⟨30573242478374733644575153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40764323304499644859433537 30573242478374733644575153)
                  ·
                    refine ⟨22929931858781050233431365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30573242478374733644575153 22929931858781050233431365)
                    ·
                      refine ⟨4299362223521446918768381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22929931858781050233431365 4299362223521446918768381)
                      ·
                        rfl

theorem cell23_8372978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_8372978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8372978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8372978 prefixEnd_8372978 := by exact prefixLift 8372978
  have htrace : WordTrace (prefixWord ++ tailWord_8372978) baseStart_8372978 baseEnd_8372978 := by
    simpa [prefixWord, tailWord_8372978, baseEnd_8372978] using wordTrace_append hprefix tailTrace_8372978
  have hstable : (prefixWord ++ tailWord_8372978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8372978).length < 2 ^ (prefixWord ++ tailWord_8372978).sum := by decide
  have hdescent : baseEnd_8372978 < baseStart_8372978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8372978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373001 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_8373001 : Nat := 118140960795 + 8373001 * 2 ^ 59
def prefixEnd_8373001 : Nat := 4983230072969 + 3 ^ 40 * 8373001 * 2
def baseEnd_8373001 : Nat := 1433124677858833442926925

theorem tailTrace_8373001 : CollatzResearch.WordTrace tailWord_8373001 prefixEnd_8373001 1433124677858833442926925 := by
  unfold tailWord_8373001
  simp only [CollatzResearch.WordTrace]
  refine ⟨305388435139054846568214857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203592290092703231045476571 305388435139054846568214857)
  ·
    refine ⟨229041326354291134926161143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305388435139054846568214857 229041326354291134926161143)
    ·
      refine ⟨343561989531436702389241715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229041326354291134926161143 343561989531436702389241715)
      ·
        refine ⟨515342984297155053583862573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343561989531436702389241715 515342984297155053583862573)
        ·
          refine ⟨193253619111433145093948465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515342984297155053583862573 193253619111433145093948465)
          ·
            refine ⟨144940214333574858820461349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193253619111433145093948465 144940214333574858820461349)
            ·
              refine ⟨27176290187545286028836503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144940214333574858820461349 27176290187545286028836503)
              ·
                refine ⟨40764435281317929043254755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27176290187545286028836503 40764435281317929043254755)
                ·
                  refine ⟨61146652921976893564882133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40764435281317929043254755 61146652921976893564882133)
                  ·
                    refine ⟨1433124677858833442926925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61146652921976893564882133 1433124677858833442926925)
                    ·
                      rfl

theorem cell23_8373001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_8373001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373001 prefixEnd_8373001 := by exact prefixLift 8373001
  have htrace : WordTrace (prefixWord ++ tailWord_8373001) baseStart_8373001 baseEnd_8373001 := by
    simpa [prefixWord, tailWord_8373001, baseEnd_8373001] using wordTrace_append hprefix tailTrace_8373001
  have hstable : (prefixWord ++ tailWord_8373001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373001).length < 2 ^ (prefixWord ++ tailWord_8373001).sum := by decide
  have hdescent : baseEnd_8373001 < baseStart_8373001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373011 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5]
def baseStart_8373011 : Nat := 118140960795 + 8373011 * 2 ^ 59
def prefixEnd_8373011 : Nat := 4983230072969 + 3 ^ 40 * 8373011 * 2
def baseEnd_8373011 : Nat := 4299379168383045289655729

theorem tailTrace_8373011 : CollatzResearch.WordTrace tailWord_8373011 prefixEnd_8373011 4299379168383045289655729 := by
  unfold tailWord_8373011
  simp only [CollatzResearch.WordTrace]
  refine ⟨305388799869018618276078887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203592533246012412184052591 305388799869018618276078887)
  ·
    refine ⟨458083199803527927414118331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305388799869018618276078887 458083199803527927414118331)
    ·
      refine ⟨687124799705291891121177497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458083199803527927414118331 687124799705291891121177497)
      ·
        refine ⟨515343599778968918340883123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687124799705291891121177497 515343599778968918340883123)
        ·
          refine ⟨773015399668453377511324685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515343599778968918340883123 773015399668453377511324685)
          ·
            refine ⟨289880774875670016566746757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 773015399668453377511324685 289880774875670016566746757)
            ·
              refine ⟨54352645289188128106265017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289880774875670016566746757 54352645289188128106265017)
              ·
                refine ⟨40764483966891096079698763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54352645289188128106265017 40764483966891096079698763)
                ·
                  refine ⟨61146725950336644119548145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40764483966891096079698763 61146725950336644119548145)
                  ·
                    refine ⟨45860044462752483089661109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61146725950336644119548145 45860044462752483089661109)
                    ·
                      refine ⟨4299379168383045289655729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45860044462752483089661109 4299379168383045289655729)
                      ·
                        rfl

theorem cell23_8373011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_8373011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373011 prefixEnd_8373011 := by exact prefixLift 8373011
  have htrace : WordTrace (prefixWord ++ tailWord_8373011) baseStart_8373011 baseEnd_8373011 := by
    simpa [prefixWord, tailWord_8373011, baseEnd_8373011] using wordTrace_append hprefix tailTrace_8373011
  have hstable : (prefixWord ++ tailWord_8373011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373011).length < 2 ^ (prefixWord ++ tailWord_8373011).sum := by decide
  have hdescent : baseEnd_8373011 < baseStart_8373011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373018 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_8373018 : Nat := 118140960795 + 8373018 * 2 ^ 59
def prefixEnd_8373018 : Nat := 4983230072969 + 3 ^ 40 * 8373018 * 2
def baseEnd_8373018 : Nat := 1433127587582542254089399

theorem tailTrace_8373018 : CollatzResearch.WordTrace tailWord_8373018 prefixEnd_8373018 1433127587582542254089399 := by
  unfold tailWord_8373018
  simp only [CollatzResearch.WordTrace]
  refine ⟨76347263794998314617895927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203592703453328838981055805 76347263794998314617895927)
  ·
    refine ⟨114520895692497471926843891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76347263794998314617895927 114520895692497471926843891)
    ·
      refine ⟨171781343538746207890265837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114520895692497471926843891 171781343538746207890265837)
      ·
        refine ⟨64418003827029827958849689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171781343538746207890265837 64418003827029827958849689)
        ·
          refine ⟨48313502870272370969137267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64418003827029827958849689 48313502870272370969137267)
          ·
            refine ⟨72470254305408556453705901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48313502870272370969137267 72470254305408556453705901)
            ·
              refine ⟨27176345364528208670139713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72470254305408556453705901 27176345364528208670139713)
              ·
                refine ⟨20382259023396156502604785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27176345364528208670139713 20382259023396156502604785)
                ·
                  refine ⟨15286694267547117376953589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20382259023396156502604785 15286694267547117376953589)
                  ·
                    refine ⟨1433127587582542254089399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15286694267547117376953589 1433127587582542254089399)
                    ·
                      rfl

theorem cell23_8373018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_8373018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373018 prefixEnd_8373018 := by exact prefixLift 8373018
  have htrace : WordTrace (prefixWord ++ tailWord_8373018) baseStart_8373018 baseEnd_8373018 := by
    simpa [prefixWord, tailWord_8373018, baseEnd_8373018] using wordTrace_append hprefix tailTrace_8373018
  have hstable : (prefixWord ++ tailWord_8373018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373018).length < 2 ^ (prefixWord ++ tailWord_8373018).sum := by decide
  have hdescent : baseEnd_8373018 < baseStart_8373018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373048 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_8373048 : Nat := 118140960795 + 8373048 * 2 ^ 59
def prefixEnd_8373048 : Nat := 4983230072969 + 3 ^ 40 * 8373048 * 2
def baseEnd_8373048 : Nat := 1433132722389087214964353

theorem tailTrace_8373048 : CollatzResearch.WordTrace tailWord_8373048 prefixEnd_8373048 1433132722389087214964353 := by
  unfold tailWord_8373048
  simp only [CollatzResearch.WordTrace]
  refine ⟨152695074684942286797587899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203593432913256382396783865 152695074684942286797587899)
  ·
    refine ⟨229042612027413430196381849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152695074684942286797587899 229042612027413430196381849)
    ·
      refine ⟨171781959020560072647286387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229042612027413430196381849 171781959020560072647286387)
      ·
        refine ⟨257672938530840108970929581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171781959020560072647286387 257672938530840108970929581)
        ·
          refine ⟨96627351949065040864098593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257672938530840108970929581 96627351949065040864098593)
          ·
            refine ⟨72470513961798780648073945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96627351949065040864098593 72470513961798780648073945)
            ·
              refine ⟨54352885471349085486055459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72470513961798780648073945 54352885471349085486055459)
              ·
                refine ⟨81529328207023628229083189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54352885471349085486055459 81529328207023628229083189)
                ·
                  refine ⟨7643374519408465146476549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81529328207023628229083189 7643374519408465146476549)
                  ·
                    refine ⟨1433132722389087214964353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643374519408465146476549 1433132722389087214964353)
                    ·
                      rfl

theorem cell23_8373048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_8373048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373048 prefixEnd_8373048 := by exact prefixLift 8373048
  have htrace : WordTrace (prefixWord ++ tailWord_8373048) baseStart_8373048 baseEnd_8373048 := by
    simpa [prefixWord, tailWord_8373048, baseEnd_8373048] using wordTrace_append hprefix tailTrace_8373048
  have hstable : (prefixWord ++ tailWord_8373048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373048).length < 2 ^ (prefixWord ++ tailWord_8373048).sum := by decide
  have hdescent : baseEnd_8373048 < baseStart_8373048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373055 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_8373055 : Nat := 118140960795 + 8373055 * 2 ^ 59
def prefixEnd_8373055 : Nat := 4983230072969 + 3 ^ 40 * 8373055 * 2
def baseEnd_8373055 : Nat := 4299401761531843117505527

theorem tailTrace_8373055 : CollatzResearch.WordTrace tailWord_8373055 prefixEnd_8373055 4299401761531843117505527 := by
  unfold tailWord_8373055
  simp only [CollatzResearch.WordTrace]
  refine ⟨305390404680859213790680619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203593603120572809193787079 305390404680859213790680619)
  ·
    refine ⟨458085607021288820686020929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305390404680859213790680619 458085607021288820686020929)
    ·
      refine ⟨343564205265966615514515697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458085607021288820686020929 343564205265966615514515697)
      ·
        refine ⟨257673153949474961635886773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343564205265966615514515697 257673153949474961635886773)
        ·
          refine ⟨24156858182763277653364385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257673153949474961635886773 24156858182763277653364385)
          ·
            refine ⟨18117643637072458240023289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156858182763277653364385 18117643637072458240023289)
            ·
              refine ⟨13588232727804343680017467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18117643637072458240023289 13588232727804343680017467)
              ·
                refine ⟨20382349091706515520026201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13588232727804343680017467 20382349091706515520026201)
                ·
                  refine ⟨15286761818779886640019651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20382349091706515520026201 15286761818779886640019651)
                  ·
                    refine ⟨22930142728169829960029477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15286761818779886640019651 22930142728169829960029477)
                    ·
                      refine ⟨4299401761531843117505527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22930142728169829960029477 4299401761531843117505527)
                      ·
                        rfl

theorem cell23_8373055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_8373055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373055 prefixEnd_8373055 := by exact prefixLift 8373055
  have htrace : WordTrace (prefixWord ++ tailWord_8373055) baseStart_8373055 baseEnd_8373055 := by
    simpa [prefixWord, tailWord_8373055, baseEnd_8373055] using wordTrace_append hprefix tailTrace_8373055
  have hstable : (prefixWord ++ tailWord_8373055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373055).length < 2 ^ (prefixWord ++ tailWord_8373055).sum := by decide
  have hdescent : baseEnd_8373055 < baseStart_8373055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373061 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 8]
def baseStart_8373061 : Nat := 118140960795 + 8373061 * 2 ^ 59
def prefixEnd_8373061 : Nat := 4983230072969 + 3 ^ 40 * 8373061 * 2
def baseEnd_8373061 : Nat := 477711649157307788225611

theorem tailTrace_8373061 : CollatzResearch.WordTrace tailWord_8373061 prefixEnd_8373061 477711649157307788225611 := by
  unfold tailWord_8373061
  simp only [CollatzResearch.WordTrace]
  refine ⟨305390623518837476815399037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203593749012558317876932691 305390623518837476815399037)
  ·
    refine ⟨114521483819564053805774639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305390623518837476815399037 114521483819564053805774639)
    ·
      refine ⟨171782225729346080708661959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114521483819564053805774639 171782225729346080708661959)
      ·
        refine ⟨257673338594019121062992939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171782225729346080708661959 257673338594019121062992939)
        ·
          refine ⟨386510007891028681594489409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257673338594019121062992939 386510007891028681594489409)
          ·
            refine ⟨289882505918271511195867057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386510007891028681594489409 289882505918271511195867057)
            ·
              refine ⟨217411879438703633396900293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289882505918271511195867057 217411879438703633396900293)
              ·
                refine ⟨40764727394756931261918805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217411879438703633396900293 40764727394756931261918805)
                ·
                  refine ⟨477711649157307788225611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40764727394756931261918805 477711649157307788225611)
                  ·
                    rfl

theorem cell23_8373061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_8373061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373061 prefixEnd_8373061 := by exact prefixLift 8373061
  have htrace : WordTrace (prefixWord ++ tailWord_8373061) baseStart_8373061 baseEnd_8373061 := by
    simpa [prefixWord, tailWord_8373061, baseEnd_8373061] using wordTrace_append hprefix tailTrace_8373061
  have hstable : (prefixWord ++ tailWord_8373061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373061).length < 2 ^ (prefixWord ++ tailWord_8373061).sum := by decide
  have hdescent : baseEnd_8373061 < baseStart_8373061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373082 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_8373082 : Nat := 118140960795 + 8373082 * 2 ^ 59
def prefixEnd_8373082 : Nat := 4983230072969 + 3 ^ 40 * 8373082 * 2
def baseEnd_8373082 : Nat := 1433138541836504837289301

theorem tailTrace_8373082 : CollatzResearch.WordTrace tailWord_8373082 prefixEnd_8373082 1433138541836504837289301 := by
  unfold tailWord_8373082
  simp only [CollatzResearch.WordTrace]
  refine ⟨76347847362940349350478375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203594259634507598267942333 76347847362940349350478375)
  ·
    refine ⟨114521771044410524025717563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76347847362940349350478375 114521771044410524025717563)
    ·
      refine ⟨171782656566615786038576345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114521771044410524025717563 171782656566615786038576345)
      ·
        refine ⟨128836992424961839528932259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171782656566615786038576345 128836992424961839528932259)
        ·
          refine ⟨193255488637442759293398389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128836992424961839528932259 193255488637442759293398389)
          ·
            refine ⟨18117702059760258683756099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193255488637442759293398389 18117702059760258683756099)
            ·
              refine ⟨27176553089640388025634149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117702059760258683756099 27176553089640388025634149)
              ·
                refine ⟨5095603704307572754806403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27176553089640388025634149 5095603704307572754806403)
                ·
                  refine ⟨7643405556461359132209605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095603704307572754806403 7643405556461359132209605)
                  ·
                    refine ⟨1433138541836504837289301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643405556461359132209605 1433138541836504837289301)
                    ·
                      rfl

theorem cell23_8373082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_8373082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373082 prefixEnd_8373082 := by exact prefixLift 8373082
  have htrace : WordTrace (prefixWord ++ tailWord_8373082) baseStart_8373082 baseEnd_8373082 := by
    simpa [prefixWord, tailWord_8373082, baseEnd_8373082] using wordTrace_append hprefix tailTrace_8373082
  have hstable : (prefixWord ++ tailWord_8373082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373082).length < 2 ^ (prefixWord ++ tailWord_8373082).sum := by decide
  have hdescent : baseEnd_8373082 < baseStart_8373082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373105 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_8373105 : Nat := 118140960795 + 8373105 * 2 ^ 59
def prefixEnd_8373105 : Nat := 4983230072969 + 3 ^ 40 * 8373105 * 2
def baseEnd_8373105 : Nat := 4299427435564567921880297

theorem tailTrace_8373105 : CollatzResearch.WordTrace tailWord_8373105 prefixEnd_8373105 4299427435564567921880297 := by
  unfold tailWord_8373105
  simp only [CollatzResearch.WordTrace]
  refine ⟨305392228330678072330000769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203594818887118714886667179 305392228330678072330000769)
  ·
    refine ⟨229044171248008554247500577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305392228330678072330000769 229044171248008554247500577)
    ·
      refine ⟨171783128436006415685625433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229044171248008554247500577 171783128436006415685625433)
      ·
        refine ⟨128837346327004811764219075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171783128436006415685625433 128837346327004811764219075)
        ·
          refine ⟨193256019490507217646328613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128837346327004811764219075 193256019490507217646328613)
          ·
            refine ⟨36235503654470103308686615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193256019490507217646328613 36235503654470103308686615)
            ·
              refine ⟨54353255481705154963029923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36235503654470103308686615 54353255481705154963029923)
              ·
                refine ⟨81529883222557732444544885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54353255481705154963029923 81529883222557732444544885)
                ·
                  refine ⟨7643426552114787416676083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81529883222557732444544885 7643426552114787416676083)
                  ·
                    refine ⟨11465139828172181125014125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7643426552114787416676083 11465139828172181125014125)
                    ·
                      refine ⟨4299427435564567921880297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11465139828172181125014125 4299427435564567921880297)
                      ·
                        rfl

theorem cell23_8373105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_8373105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373105 prefixEnd_8373105 := by exact prefixLift 8373105
  have htrace : WordTrace (prefixWord ++ tailWord_8373105) baseStart_8373105 baseEnd_8373105 := by
    simpa [prefixWord, tailWord_8373105, baseEnd_8373105] using wordTrace_append hprefix tailTrace_8373105
  have hstable : (prefixWord ++ tailWord_8373105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373105).length < 2 ^ (prefixWord ++ tailWord_8373105).sum := by decide
  have hdescent : baseEnd_8373105 < baseStart_8373105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373125 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_8373125 : Nat := 118140960795 + 8373125 * 2 ^ 59
def prefixEnd_8373125 : Nat := 4983230072969 + 3 ^ 40 * 8373125 * 2
def baseEnd_8373125 : Nat := 1433145901725885947876735

theorem tailTrace_8373125 : CollatzResearch.WordTrace tailWord_8373125 prefixEnd_8373125 1433145901725885947876735 := by
  unfold tailWord_8373125
  simp only [CollatzResearch.WordTrace]
  refine ⟨305392957790605615745728829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203595305193737077163819219 305392957790605615745728829)
  ·
    refine ⟨114522359171477105904648311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305392957790605615745728829 114522359171477105904648311)
    ·
      refine ⟨171783538757215658856972467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114522359171477105904648311 171783538757215658856972467)
      ·
        refine ⟨257675308135823488285458701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171783538757215658856972467 257675308135823488285458701)
        ·
          refine ⟨96628240550933808107047013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257675308135823488285458701 96628240550933808107047013)
          ·
            refine ⟨18117795103300089020071315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96628240550933808107047013 18117795103300089020071315)
            ·
              refine ⟨27176692654950133530106973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18117795103300089020071315 27176692654950133530106973)
              ·
                refine ⟨10191259745606300073790115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27176692654950133530106973 10191259745606300073790115)
                ·
                  refine ⟨15286889618409450110685173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191259745606300073790115 15286889618409450110685173)
                  ·
                    refine ⟨1433145901725885947876735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15286889618409450110685173 1433145901725885947876735)
                    ·
                      rfl

theorem cell23_8373125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_8373125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373125 prefixEnd_8373125 := by exact prefixLift 8373125
  have htrace : WordTrace (prefixWord ++ tailWord_8373125) baseStart_8373125 baseEnd_8373125 := by
    simpa [prefixWord, tailWord_8373125, baseEnd_8373125] using wordTrace_append hprefix tailTrace_8373125
  have hstable : (prefixWord ++ tailWord_8373125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373125).length < 2 ^ (prefixWord ++ tailWord_8373125).sum := by decide
  have hdescent : baseEnd_8373125 < baseStart_8373125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373155 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 2, 4]
def baseStart_8373155 : Nat := 118140960795 + 8373155 * 2 ^ 59
def prefixEnd_8373155 : Nat := 4983230072969 + 3 ^ 40 * 8373155 * 2
def baseEnd_8373155 : Nat := 1433151036532430908751689

theorem tailTrace_8373155 : CollatzResearch.WordTrace tailWord_8373155 prefixEnd_8373155 1433151036532430908751689 := by
  unfold tailWord_8373155
  simp only [CollatzResearch.WordTrace]
  refine ⟨305394051980496930869320919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203596034653664620579547279 305394051980496930869320919)
  ·
    refine ⟨458091077970745396303981379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305394051980496930869320919 458091077970745396303981379)
    ·
      refine ⟨687136616956118094455972069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458091077970745396303981379 687136616956118094455972069)
      ·
        refine ⟨128838115679272142710494763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687136616956118094455972069 128838115679272142710494763)
        ·
          refine ⟨193257173518908214065742145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128838115679272142710494763 193257173518908214065742145)
          ·
            refine ⟨144942880139181160549306609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193257173518908214065742145 144942880139181160549306609)
            ·
              refine ⟨108707160104385870411979957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144942880139181160549306609 108707160104385870411979957)
              ·
                refine ⟨10191296259786175351123121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108707160104385870411979957 10191296259786175351123121)
                ·
                  refine ⟨7643472194839631513342341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10191296259786175351123121 7643472194839631513342341)
                  ·
                    refine ⟨1433151036532430908751689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643472194839631513342341 1433151036532430908751689)
                    ·
                      rfl

theorem cell23_8373155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 4].length) (baseStart_8373155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373155 prefixEnd_8373155 := by exact prefixLift 8373155
  have htrace : WordTrace (prefixWord ++ tailWord_8373155) baseStart_8373155 baseEnd_8373155 := by
    simpa [prefixWord, tailWord_8373155, baseEnd_8373155] using wordTrace_append hprefix tailTrace_8373155
  have hstable : (prefixWord ++ tailWord_8373155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373155).length < 2 ^ (prefixWord ++ tailWord_8373155).sum := by decide
  have hdescent : baseEnd_8373155 < baseStart_8373155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373182 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_8373182 : Nat := 118140960795 + 8373182 * 2 ^ 59
def prefixEnd_8373182 : Nat := 4983230072969 + 3 ^ 40 * 8373182 * 2
def baseEnd_8373182 : Nat := 4299466973574964120617443

theorem tailTrace_8373182 : CollatzResearch.WordTrace tailWord_8373182 prefixEnd_8373182 4299466973574964120617443 := by
  unfold tailWord_8373182
  simp only [CollatzResearch.WordTrace]
  refine ⟨38174379593924889310069225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203596691167599409653702533 38174379593924889310069225)
  ·
    refine ⟨28630784695443666982551919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38174379593924889310069225 28630784695443666982551919)
    ·
      refine ⟨42946177043165500473827879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28630784695443666982551919 42946177043165500473827879)
      ·
        refine ⟨64419265564748250710741819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42946177043165500473827879 64419265564748250710741819)
        ·
          refine ⟨96628898347122376066112729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64419265564748250710741819 96628898347122376066112729)
          ·
            refine ⟨72471673760341782049584547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96628898347122376066112729 72471673760341782049584547)
            ·
              refine ⟨108707510640512673074376821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72471673760341782049584547 108707510640512673074376821)
              ·
                refine ⟨10191329122548063100722827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108707510640512673074376821 10191329122548063100722827)
                ·
                  refine ⟨15286993683822094651084241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191329122548063100722827 15286993683822094651084241)
                  ·
                    refine ⟨11465245262866570988313181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15286993683822094651084241 11465245262866570988313181)
                    ·
                      refine ⟨4299466973574964120617443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11465245262866570988313181 4299466973574964120617443)
                      ·
                        rfl

theorem cell23_8373182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_8373182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373182 prefixEnd_8373182 := by exact prefixLift 8373182
  have htrace : WordTrace (prefixWord ++ tailWord_8373182) baseStart_8373182 baseEnd_8373182 := by
    simpa [prefixWord, tailWord_8373182, baseEnd_8373182] using wordTrace_append hprefix tailTrace_8373182
  have hstable : (prefixWord ++ tailWord_8373182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373182).length < 2 ^ (prefixWord ++ tailWord_8373182).sum := by decide
  have hdescent : baseEnd_8373182 < baseStart_8373182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373206 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_8373206 : Nat := 118140960795 + 8373206 * 2 ^ 59
def prefixEnd_8373206 : Nat := 4983230072969 + 3 ^ 40 * 8373206 * 2
def baseEnd_8373206 : Nat := 1433159765703557342239111

theorem tailTrace_8373206 : CollatzResearch.WordTrace tailWord_8373206 prefixEnd_8373206 1433159765703557342239111 := by
  unfold tailWord_8373206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087244506457010411214217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203597274735541444386284981 19087244506457010411214217)
  ·
    refine ⟨14315433379842757808410663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19087244506457010411214217 14315433379842757808410663)
    ·
      refine ⟨21473150069764136712615995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14315433379842757808410663 21473150069764136712615995)
      ·
        refine ⟨32209725104646205068923993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21473150069764136712615995 32209725104646205068923993)
        ·
          refine ⟨24157293828484653801692995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32209725104646205068923993 24157293828484653801692995)
          ·
            refine ⟨36235940742726980702539493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24157293828484653801692995 36235940742726980702539493)
            ·
              refine ⟨6794238889261308881726155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36235940742726980702539493 6794238889261308881726155)
              ·
                refine ⟨10191358333891963322589233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794238889261308881726155 10191358333891963322589233)
                ·
                  refine ⟨7643518750418972491941925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10191358333891963322589233 7643518750418972491941925)
                  ·
                    refine ⟨1433159765703557342239111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643518750418972491941925 1433159765703557342239111)
                    ·
                      rfl

theorem cell23_8373206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_8373206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373206 prefixEnd_8373206 := by exact prefixLift 8373206
  have htrace : WordTrace (prefixWord ++ tailWord_8373206) baseStart_8373206 baseEnd_8373206 := by
    simpa [prefixWord, tailWord_8373206, baseEnd_8373206] using wordTrace_append hprefix tailTrace_8373206
  have hstable : (prefixWord ++ tailWord_8373206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373206).length < 2 ^ (prefixWord ++ tailWord_8373206).sum := by decide
  have hdescent : baseEnd_8373206 < baseStart_8373206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373228 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_8373228 : Nat := 118140960795 + 8373228 * 2 ^ 59
def prefixEnd_8373228 : Nat := 4983230072969 + 3 ^ 40 * 8373228 * 2
def baseEnd_8373228 : Nat := 1433163531228356980214077

theorem tailTrace_8373228 : CollatzResearch.WordTrace tailWord_8373228 prefixEnd_8373228 1433163531228356980214077 := by
  unfold tailWord_8373228
  simp only [CollatzResearch.WordTrace]
  refine ⟨152698357254616232168364169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203597809672821642891152225 152698357254616232168364169)
  ·
    refine ⟨114523767940962174126273127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152698357254616232168364169 114523767940962174126273127)
    ·
      refine ⟨171785651911443261189409691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114523767940962174126273127 171785651911443261189409691)
      ·
        refine ⟨257678477867164891784114537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171785651911443261189409691 257678477867164891784114537)
        ·
          refine ⟨193258858400373668838085903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257678477867164891784114537 193258858400373668838085903)
          ·
            refine ⟨289888287600560503257128855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193258858400373668838085903 289888287600560503257128855)
            ·
              refine ⟨434832431400840754885693283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289888287600560503257128855 434832431400840754885693283)
              ·
                refine ⟨652248647101261132328539925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434832431400840754885693283 652248647101261132328539925)
                ·
                  refine ⟨30574155332871615577900309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 652248647101261132328539925 30574155332871615577900309)
                  ·
                    refine ⟨1433163531228356980214077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30574155332871615577900309 1433163531228356980214077)
                    ·
                      rfl

theorem cell23_8373228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_8373228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373228 prefixEnd_8373228 := by exact prefixLift 8373228
  have htrace : WordTrace (prefixWord ++ tailWord_8373228) baseStart_8373228 baseEnd_8373228 := by
    simpa [prefixWord, tailWord_8373228, baseEnd_8373228] using wordTrace_append hprefix tailTrace_8373228
  have hstable : (prefixWord ++ tailWord_8373228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373228).length < 2 ^ (prefixWord ++ tailWord_8373228).sum := by decide
  have hdescent : baseEnd_8373228 < baseStart_8373228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373236 : List Nat := [2, 6, 2, 1, 2, 10]
def baseStart_8373236 : Nat := 118140960795 + 8373236 * 2 ^ 59
def prefixEnd_8373236 : Nat := 4983230072969 + 3 ^ 40 * 8373236 * 2
def baseEnd_8373236 : Nat := 17693393833458053124865

theorem tailTrace_8373236 : CollatzResearch.WordTrace tailWord_8373236 prefixEnd_8373236 17693393833458053124865 := by
  unfold tailWord_8373236
  simp only [CollatzResearch.WordTrace]
  refine ⟨152698503146601740851509781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203598004195468987802013041 152698503146601740851509781)
  ·
    refine ⟨7157742334996956602414521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152698503146601740851509781 7157742334996956602414521)
    ·
      refine ⟨5368306751247717451810891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7157742334996956602414521 5368306751247717451810891)
      ·
        refine ⟨8052460126871576177716337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368306751247717451810891 8052460126871576177716337)
        ·
          refine ⟨6039345095153682133287253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8052460126871576177716337 6039345095153682133287253)
          ·
            refine ⟨17693393833458053124865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6039345095153682133287253 17693393833458053124865)
            ·
              rfl

theorem cell23_8373236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 10].length) (baseStart_8373236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373236 prefixEnd_8373236 := by exact prefixLift 8373236
  have htrace : WordTrace (prefixWord ++ tailWord_8373236) baseStart_8373236 baseEnd_8373236 := by
    simpa [prefixWord, tailWord_8373236, baseEnd_8373236] using wordTrace_append hprefix tailTrace_8373236
  have hstable : (prefixWord ++ tailWord_8373236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373236).length < 2 ^ (prefixWord ++ tailWord_8373236).sum := by decide
  have hdescent : baseEnd_8373236 < baseStart_8373236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373255 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_8373255 : Nat := 118140960795 + 8373255 * 2 ^ 59
def prefixEnd_8373255 : Nat := 4983230072969 + 3 ^ 40 * 8373255 * 2
def baseEnd_8373255 : Nat := 4299504457662742335004607

theorem tailTrace_8373255 : CollatzResearch.WordTrace tailWord_8373255 prefixEnd_8373255 4299504457662742335004607 := by
  unfold tailWord_8373255
  simp only [CollatzResearch.WordTrace]
  refine ⟨305397699280134647947961219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203598466186756431965307479 305397699280134647947961219)
  ·
    refine ⟨458096548920201971921941829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305397699280134647947961219 458096548920201971921941829)
    ·
      refine ⟨85893102922537869735364093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458096548920201971921941829 85893102922537869735364093)
      ·
        refine ⟨32209913595951701150761535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85893102922537869735364093 32209913595951701150761535)
        ·
          refine ⟨48314870393927551726142303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32209913595951701150761535 48314870393927551726142303)
          ·
            refine ⟨72472305590891327589213455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48314870393927551726142303 72472305590891327589213455)
            ·
              refine ⟨108708458386336991383820183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72472305590891327589213455 108708458386336991383820183)
              ·
                refine ⟨163062687579505487075730275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108708458386336991383820183 163062687579505487075730275)
                ·
                  refine ⟨244594031369258230613595413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163062687579505487075730275 244594031369258230613595413)
                  ·
                    refine ⟨11465345220433979560012285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244594031369258230613595413 11465345220433979560012285)
                    ·
                      refine ⟨4299504457662742335004607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11465345220433979560012285 4299504457662742335004607)
                      ·
                        rfl

theorem cell23_8373255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_8373255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373255 prefixEnd_8373255 := by exact prefixLift 8373255
  have htrace : WordTrace (prefixWord ++ tailWord_8373255) baseStart_8373255 baseEnd_8373255 := by
    simpa [prefixWord, tailWord_8373255, baseEnd_8373255] using wordTrace_append hprefix tailTrace_8373255
  have hstable : (prefixWord ++ tailWord_8373255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373255).length < 2 ^ (prefixWord ++ tailWord_8373255).sum := by decide
  have hdescent : baseEnd_8373255 < baseStart_8373255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373269 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_8373269 : Nat := 118140960795 + 8373269 * 2 ^ 59
def prefixEnd_8373269 : Nat := 4983230072969 + 3 ^ 40 * 8373269 * 2
def baseEnd_8373269 : Nat := 4299511646391905280229543

theorem tailTrace_8373269 : CollatzResearch.WordTrace tailWord_8373269 prefixEnd_8373269 4299511646391905280229543 := by
  unfold tailWord_8373269
  simp only [CollatzResearch.WordTrace]
  refine ⟨305398209902083928338970861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203598806601389285559313907 305398209902083928338970861)
  ·
    refine ⟨114524328713281473127114073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305398209902083928338970861 114524328713281473127114073)
    ·
      refine ⟨85893246534961104845335555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114524328713281473127114073 85893246534961104845335555)
      ·
        refine ⟨128839869802441657268003333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85893246534961104845335555 128839869802441657268003333)
        ·
          refine ⟨24157475587957810737750625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128839869802441657268003333 24157475587957810737750625)
          ·
            refine ⟨18118106690968358053312969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24157475587957810737750625 18118106690968358053312969)
            ·
              refine ⟨13588580018226268539984727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18118106690968358053312969 13588580018226268539984727)
              ·
                refine ⟨20382870027339402809977091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13588580018226268539984727 20382870027339402809977091)
                ·
                  refine ⟨30574305041009104214965637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20382870027339402809977091 30574305041009104214965637)
                  ·
                    refine ⟨5732682195189207040306057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30574305041009104214965637 5732682195189207040306057)
                    ·
                      refine ⟨4299511646391905280229543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732682195189207040306057 4299511646391905280229543)
                      ·
                        rfl

theorem cell23_8373269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_8373269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373269 prefixEnd_8373269 := by exact prefixLift 8373269
  have htrace : WordTrace (prefixWord ++ tailWord_8373269) baseStart_8373269 baseEnd_8373269 := by
    simpa [prefixWord, tailWord_8373269, baseEnd_8373269] using wordTrace_append hprefix tailTrace_8373269
  have hstable : (prefixWord ++ tailWord_8373269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373269).length < 2 ^ (prefixWord ++ tailWord_8373269).sum := by decide
  have hdescent : baseEnd_8373269 < baseStart_8373269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373285 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_8373285 : Nat := 118140960795 + 8373285 * 2 ^ 59
def prefixEnd_8373285 : Nat := 4983230072969 + 3 ^ 40 * 8373285 * 2
def baseEnd_8373285 : Nat := 4299519862082377217629469

theorem tailTrace_8373285 : CollatzResearch.WordTrace tailWord_8373285 prefixEnd_8373285 4299519862082377217629469 := by
  unfold tailWord_8373285
  simp only [CollatzResearch.WordTrace]
  refine ⟨305398793470025963071553309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203599195646683975381035539 305398793470025963071553309)
  ·
    refine ⟨114524547551259736151832491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305398793470025963071553309 114524547551259736151832491)
    ·
      refine ⟨171786821326889604227748737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114524547551259736151832491 171786821326889604227748737)
      ·
        refine ⟨128840115995167203170811553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171786821326889604227748737 128840115995167203170811553)
        ·
          refine ⟨96630086996375402378108665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128840115995167203170811553 96630086996375402378108665)
          ·
            refine ⟨72472565247281551783581499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96630086996375402378108665 72472565247281551783581499)
            ·
              refine ⟨108708847870922327675372249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72472565247281551783581499 108708847870922327675372249)
              ·
                refine ⟨81531635903191745756529187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108708847870922327675372249 81531635903191745756529187)
                ·
                  refine ⟨122297453854787618634793781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81531635903191745756529187 122297453854787618634793781)
                  ·
                    refine ⟨11465386298886339247011917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122297453854787618634793781 11465386298886339247011917)
                    ·
                      refine ⟨4299519862082377217629469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11465386298886339247011917 4299519862082377217629469)
                      ·
                        rfl

theorem cell23_8373285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_8373285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373285 prefixEnd_8373285 := by exact prefixLift 8373285
  have htrace : WordTrace (prefixWord ++ tailWord_8373285) baseStart_8373285 baseEnd_8373285 := by
    simpa [prefixWord, tailWord_8373285, baseEnd_8373285] using wordTrace_append hprefix tailTrace_8373285
  have hstable : (prefixWord ++ tailWord_8373285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373285).length < 2 ^ (prefixWord ++ tailWord_8373285).sum := by decide
  have hdescent : baseEnd_8373285 < baseStart_8373285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373290 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_8373290 : Nat := 118140960795 + 8373290 * 2 ^ 59
def prefixEnd_8373290 : Nat := 4983230072969 + 3 ^ 40 * 8373290 * 2
def baseEnd_8373290 : Nat := 4299522429485649698066947

theorem tailTrace_8373290 : CollatzResearch.WordTrace tailWord_8373290 prefixEnd_8373290 4299522429485649698066947 := by
  unfold tailWord_8373290
  simp only [CollatzResearch.WordTrace]
  refine ⟨76349743958751962231371331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203599317223338565950323549 76349743958751962231371331)
  ·
    refine ⟨114524615938127943347056997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76349743958751962231371331 114524615938127943347056997)
    ·
      refine ⟨21473365488398989377573187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114524615938127943347056997 21473365488398989377573187)
      ·
        refine ⟨32210048232598484066359781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21473365488398989377573187 32210048232598484066359781)
        ·
          refine ⟨6039384043612215762442459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32210048232598484066359781 6039384043612215762442459)
          ·
            refine ⟨9059076065418323643663689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039384043612215762442459 9059076065418323643663689)
            ·
              refine ⟨6794307049063742732747767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059076065418323643663689 6794307049063742732747767)
              ·
                refine ⟨10191460573595614099121651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794307049063742732747767 10191460573595614099121651)
                ·
                  refine ⟨15287190860393421148682477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191460573595614099121651 15287190860393421148682477)
                  ·
                    refine ⟨5732696572647532930755929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15287190860393421148682477 5732696572647532930755929)
                    ·
                      refine ⟨4299522429485649698066947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732696572647532930755929 4299522429485649698066947)
                      ·
                        rfl

theorem cell23_8373290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_8373290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373290 prefixEnd_8373290 := by exact prefixLift 8373290
  have htrace : WordTrace (prefixWord ++ tailWord_8373290) baseStart_8373290 baseEnd_8373290 := by
    simpa [prefixWord, tailWord_8373290, baseEnd_8373290] using wordTrace_append hprefix tailTrace_8373290
  have hstable : (prefixWord ++ tailWord_8373290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373290).length < 2 ^ (prefixWord ++ tailWord_8373290).sum := by decide
  have hdescent : baseEnd_8373290 < baseStart_8373290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373292 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 5]
def baseStart_8373292 : Nat := 118140960795 + 8373292 * 2 ^ 59
def prefixEnd_8373292 : Nat := 4983230072969 + 3 ^ 40 * 8373292 * 2
def baseEnd_8373292 : Nat := 477724828494106521137993

theorem tailTrace_8373292 : CollatzResearch.WordTrace tailWord_8373292 prefixEnd_8373292 477724828494106521137993 := by
  unfold tailWord_8373292
  simp only [CollatzResearch.WordTrace]
  refine ⟨152699524390500301633529065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203599365854000402178038753 152699524390500301633529065)
  ·
    refine ⟨114524643292875226225146799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152699524390500301633529065 114524643292875226225146799)
    ·
      refine ⟨171786964939312839337720199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114524643292875226225146799 171786964939312839337720199)
      ·
        refine ⟨257680447408969259006580299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171786964939312839337720199 257680447408969259006580299)
        ·
          refine ⟨386520671113453888509870449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257680447408969259006580299 386520671113453888509870449)
          ·
            refine ⟨289890503335090416382402837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386520671113453888509870449 289890503335090416382402837)
            ·
              refine ⟨13588617343832363267925133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289890503335090416382402837 13588617343832363267925133)
              ·
                refine ⟨5095731503937136225471925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13588617343832363267925133 5095731503937136225471925)
                ·
                  refine ⟨477724828494106521137993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5095731503937136225471925 477724828494106521137993)
                  ·
                    rfl

theorem cell23_8373292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_8373292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373292 prefixEnd_8373292 := by exact prefixLift 8373292
  have htrace : WordTrace (prefixWord ++ tailWord_8373292) baseStart_8373292 baseEnd_8373292 := by
    simpa [prefixWord, tailWord_8373292, baseEnd_8373292] using wordTrace_append hprefix tailTrace_8373292
  have hstable : (prefixWord ++ tailWord_8373292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373292).length < 2 ^ (prefixWord ++ tailWord_8373292).sum := by decide
  have hdescent : baseEnd_8373292 < baseStart_8373292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373483 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 1, 2, 2]
def baseStart_8373483 : Nat := 118140960795 + 8373483 * 2 ^ 59
def prefixEnd_8373483 : Nat := 4983230072969 + 3 ^ 40 * 8373483 * 2
def baseEnd_8373483 : Nat := 4299621531251967442953559

theorem tailTrace_8373483 : CollatzResearch.WordTrace tailWord_8373483 prefixEnd_8373483 4299621531251967442953559 := by
  unfold tailWord_8373483
  simp only [CollatzResearch.WordTrace]
  refine ⟨305406015123308642887261103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203604010082205761924840735 305406015123308642887261103)
  ·
    refine ⟨458109022684962964330891655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305406015123308642887261103 458109022684962964330891655)
    ·
      refine ⟨687163534027444446496337483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458109022684962964330891655 687163534027444446496337483)
      ·
        refine ⟨1030745301041166669744506225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687163534027444446496337483 1030745301041166669744506225)
        ·
          refine ⟨773058975780875002308379669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030745301041166669744506225 773058975780875002308379669)
          ·
            refine ⟨36237139489728515733205297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 773058975780875002308379669 36237139489728515733205297)
            ·
              refine ⟨27177854617296386799903973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36237139489728515733205297 27177854617296386799903973)
              ·
                refine ⟨5095847740743072524981995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27177854617296386799903973 5095847740743072524981995)
                ·
                  refine ⟨7643771611114608787472993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095847740743072524981995 7643771611114608787472993)
                  ·
                    refine ⟨5732828708335956590604745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643771611114608787472993 5732828708335956590604745)
                    ·
                      refine ⟨4299621531251967442953559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732828708335956590604745 4299621531251967442953559)
                      ·
                        rfl

theorem cell23_8373483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 1, 2, 2].length) (baseStart_8373483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373483 prefixEnd_8373483 := by exact prefixLift 8373483
  have htrace : WordTrace (prefixWord ++ tailWord_8373483) baseStart_8373483 baseEnd_8373483 := by
    simpa [prefixWord, tailWord_8373483, baseEnd_8373483] using wordTrace_append hprefix tailTrace_8373483
  have hstable : (prefixWord ++ tailWord_8373483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373483).length < 2 ^ (prefixWord ++ tailWord_8373483).sum := by decide
  have hdescent : baseEnd_8373483 < baseStart_8373483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373532 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_8373532 : Nat := 118140960795 + 8373532 * 2 ^ 59
def prefixEnd_8373532 : Nat := 4983230072969 + 3 ^ 40 * 8373532 * 2
def baseEnd_8373532 : Nat := 1433215563934679250413611

theorem tailTrace_8373532 : CollatzResearch.WordTrace tailWord_8373532 prefixEnd_8373532 1433215563934679250413611 := by
  unfold tailWord_8373532
  simp only [CollatzResearch.WordTrace]
  refine ⟨152703901150065562127897425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203605201533420749503863233 152703901150065562127897425)
  ·
    refine ⟨114527925862549171595923069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152703901150065562127897425 114527925862549171595923069)
    ·
      refine ⟨42947972198455939348471151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114527925862549171595923069 42947972198455939348471151)
      ·
        refine ⟨64421958297683909022706727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42947972198455939348471151 64421958297683909022706727)
        ·
          refine ⟨96632937446525863534060091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64421958297683909022706727 96632937446525863534060091)
          ·
            refine ⟨144949406169788795301090137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96632937446525863534060091 144949406169788795301090137)
            ·
              refine ⟨108712054627341596475817603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144949406169788795301090137 108712054627341596475817603)
              ·
                refine ⟨163068081941012394713726405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108712054627341596475817603 163068081941012394713726405)
                ·
                  refine ⟨30575265363939824008823701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163068081941012394713726405 30575265363939824008823701)
                  ·
                    refine ⟨1433215563934679250413611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30575265363939824008823701 1433215563934679250413611)
                    ·
                      rfl

theorem cell23_8373532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_8373532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373532 prefixEnd_8373532 := by exact prefixLift 8373532
  have htrace : WordTrace (prefixWord ++ tailWord_8373532) baseStart_8373532 baseEnd_8373532 := by
    simpa [prefixWord, tailWord_8373532, baseEnd_8373532] using wordTrace_append hprefix tailTrace_8373532
  have hstable : (prefixWord ++ tailWord_8373532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373532).length < 2 ^ (prefixWord ++ tailWord_8373532).sum := by decide
  have hdescent : baseEnd_8373532 < baseStart_8373532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373534 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_8373534 : Nat := 118140960795 + 8373534 * 2 ^ 59
def prefixEnd_8373534 : Nat := 4983230072969 + 3 ^ 40 * 8373534 * 2
def baseEnd_8373534 : Nat := 4299647718765346743415825

theorem tailTrace_8373534 : CollatzResearch.WordTrace tailWord_8373534 prefixEnd_8373534 4299647718765346743415825 := by
  unfold tailWord_8373534
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175984405765484824670957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203605250164082585731578437 38175984405765484824670957)
  ·
    refine ⟨14315994152162056809251609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38175984405765484824670957 14315994152162056809251609)
    ·
      refine ⟨10736995614121542606938707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14315994152162056809251609 10736995614121542606938707)
      ·
        refine ⟨16105493421182313910408061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736995614121542606938707 16105493421182313910408061)
        ·
          refine ⟨6039560032943367716403023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16105493421182313910408061 6039560032943367716403023)
          ·
            refine ⟨9059340049415051574604535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039560032943367716403023 9059340049415051574604535)
            ·
              refine ⟨13589010074122577361906803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059340049415051574604535 13589010074122577361906803)
              ·
                refine ⟨20383515111183866042860205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589010074122577361906803 20383515111183866042860205)
                ·
                  refine ⟨7643818166693949766072577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20383515111183866042860205 7643818166693949766072577)
                  ·
                    refine ⟨5732863625020462324554433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7643818166693949766072577 5732863625020462324554433)
                    ·
                      refine ⟨4299647718765346743415825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5732863625020462324554433 4299647718765346743415825)
                      ·
                        rfl

theorem cell23_8373534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_8373534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373534 prefixEnd_8373534 := by exact prefixLift 8373534
  have htrace : WordTrace (prefixWord ++ tailWord_8373534) baseStart_8373534 baseEnd_8373534 := by
    simpa [prefixWord, tailWord_8373534, baseEnd_8373534] using wordTrace_append hprefix tailTrace_8373534
  have hstable : (prefixWord ++ tailWord_8373534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373534).length < 2 ^ (prefixWord ++ tailWord_8373534).sum := by decide
  have hdescent : baseEnd_8373534 < baseStart_8373534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373552 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_8373552 : Nat := 118140960795 + 8373552 * 2 ^ 59
def prefixEnd_8373552 : Nat := 4983230072969 + 3 ^ 40 * 8373552 * 2
def baseEnd_8373552 : Nat := 4299656961417127672990741

theorem tailTrace_8373552 : CollatzResearch.WordTrace tailWord_8373552 prefixEnd_8373552 4299656961417127672990741 := by
  unfold tailWord_8373552
  simp only [CollatzResearch.WordTrace]
  refine ⟨152704265880029333835761455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203605687840039111781015273 152704265880029333835761455)
  ·
    refine ⟨229056398820044000753642183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152704265880029333835761455 229056398820044000753642183)
    ·
      refine ⟨343584598230066001130463275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229056398820044000753642183 343584598230066001130463275)
      ·
        refine ⟨515376897345099001695694913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343584598230066001130463275 515376897345099001695694913)
        ·
          refine ⟨386532673008824251271771185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515376897345099001695694913 386532673008824251271771185)
          ·
            refine ⟨289899504756618188453828389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386532673008824251271771185 289899504756618188453828389)
            ·
              refine ⟨54356157141865910335092823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289899504756618188453828389 54356157141865910335092823)
              ·
                refine ⟨81534235712798865502639235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54356157141865910335092823 81534235712798865502639235)
                ·
                  refine ⟨122301353569198298253958853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81534235712798865502639235 122301353569198298253958853)
                  ·
                    refine ⟨22931503794224680922617285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122301353569198298253958853 22931503794224680922617285)
                    ·
                      refine ⟨4299656961417127672990741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22931503794224680922617285 4299656961417127672990741)
                      ·
                        rfl

theorem cell23_8373552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_8373552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373552 prefixEnd_8373552 := by exact prefixLift 8373552
  have htrace : WordTrace (prefixWord ++ tailWord_8373552) baseStart_8373552 baseEnd_8373552 := by
    simpa [prefixWord, tailWord_8373552, baseEnd_8373552] using wordTrace_append hprefix tailTrace_8373552
  have hstable : (prefixWord ++ tailWord_8373552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373552).length < 2 ^ (prefixWord ++ tailWord_8373552).sum := by decide
  have hdescent : baseEnd_8373552 < baseStart_8373552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373562 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_8373562 : Nat := 118140960795 + 8373562 * 2 ^ 59
def prefixEnd_8373562 : Nat := 4983230072969 + 3 ^ 40 * 8373562 * 2
def baseEnd_8373562 : Nat := 477740232913741403762855

theorem tailTrace_8373562 : CollatzResearch.WordTrace tailWord_8373562 prefixEnd_8373562 477740232913741403762855 := by
  unfold tailWord_8373562
  simp only [CollatzResearch.WordTrace]
  refine ⟨76352224122505609844846735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203605930993348292919591293 76352224122505609844846735)
  ·
    refine ⟨114528336183758414767270103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76352224122505609844846735 114528336183758414767270103)
    ·
      refine ⟨171792504275637622150905155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114528336183758414767270103 171792504275637622150905155)
      ·
        refine ⟨257688756413456433226357733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171792504275637622150905155 257688756413456433226357733)
        ·
          refine ⟨48316641827523081229942075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257688756413456433226357733 48316641827523081229942075)
          ·
            refine ⟨72474962741284621844913113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48316641827523081229942075 72474962741284621844913113)
            ·
              refine ⟨54356222055963466383684835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72474962741284621844913113 54356222055963466383684835)
              ·
                refine ⟨81534333083945199575527253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54356222055963466383684835 81534333083945199575527253)
                ·
                  refine ⟨477740232913741403762855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81534333083945199575527253 477740232913741403762855)
                  ·
                    rfl

theorem cell23_8373562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_8373562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373562 prefixEnd_8373562 := by exact prefixLift 8373562
  have htrace : WordTrace (prefixWord ++ tailWord_8373562) baseStart_8373562 baseEnd_8373562 := by
    simpa [prefixWord, tailWord_8373562, baseEnd_8373562] using wordTrace_append hprefix tailTrace_8373562
  have hstable : (prefixWord ++ tailWord_8373562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373562).length < 2 ^ (prefixWord ++ tailWord_8373562).sum := by decide
  have hdescent : baseEnd_8373562 < baseStart_8373562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373629 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_8373629 : Nat := 118140960795 + 8373629 * 2 ^ 59
def prefixEnd_8373629 : Nat := 4983230072969 + 3 ^ 40 * 8373629 * 2
def baseEnd_8373629 : Nat := 4299696499427523871727887

theorem tailTrace_8373629 : CollatzResearch.WordTrace tailWord_8373629 prefixEnd_8373629 4299696499427523871727887 := by
  unfold tailWord_8373629
  simp only [CollatzResearch.WordTrace]
  refine ⟨305411340180779709822075941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203607560120519806548050627 305411340180779709822075941)
  ·
    refine ⟨57264626283896195591639239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305411340180779709822075941 57264626283896195591639239)
    ·
      refine ⟨85896939425844293387458859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57264626283896195591639239 85896939425844293387458859)
      ·
        refine ⟨128845409138766440081188289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85896939425844293387458859 128845409138766440081188289)
        ·
          refine ⟨96634056854074830060891217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128845409138766440081188289 96634056854074830060891217)
          ·
            refine ⟨72475542640556122545668413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96634056854074830060891217 72475542640556122545668413)
            ·
              refine ⟨27178328490208545954625655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72475542640556122545668413 27178328490208545954625655)
              ·
                refine ⟨40767492735312818931938483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27178328490208545954625655 40767492735312818931938483)
                ·
                  refine ⟨61151239102969228397907725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40767492735312818931938483 61151239102969228397907725)
                  ·
                    refine ⟨22931714663613460649215397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61151239102969228397907725 22931714663613460649215397)
                    ·
                      refine ⟨4299696499427523871727887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22931714663613460649215397 4299696499427523871727887)
                      ·
                        rfl

theorem cell23_8373629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_8373629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373629 prefixEnd_8373629 := by exact prefixLift 8373629
  have htrace : WordTrace (prefixWord ++ tailWord_8373629) baseStart_8373629 baseEnd_8373629 := by
    simpa [prefixWord, tailWord_8373629, baseEnd_8373629] using wordTrace_append hprefix tailTrace_8373629
  have hstable : (prefixWord ++ tailWord_8373629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373629).length < 2 ^ (prefixWord ++ tailWord_8373629).sum := by decide
  have hdescent : baseEnd_8373629 < baseStart_8373629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373666 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_8373666 : Nat := 118140960795 + 8373666 * 2 ^ 59
def prefixEnd_8373666 : Nat := 4983230072969 + 3 ^ 40 * 8373666 * 2
def baseEnd_8373666 : Nat := 4299715498211740226965217

theorem tailTrace_8373666 : CollatzResearch.WordTrace tailWord_8373666 prefixEnd_8373666 4299715498211740226965217 := by
  unfold tailWord_8373666
  simp only [CollatzResearch.WordTrace]
  refine ⟨76353172420411416285293213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203608459787763776760781901 76353172420411416285293213)
  ·
    refine ⟨28632439657654281106984955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76353172420411416285293213 28632439657654281106984955)
    ·
      refine ⟨42948659486481421660477433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632439657654281106984955 42948659486481421660477433)
      ·
        refine ⟨32211494614861066245358075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42948659486481421660477433 32211494614861066245358075)
        ·
          refine ⟨48317241922291599368037113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32211494614861066245358075 48317241922291599368037113)
          ·
            refine ⟨36237931441718699526027835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48317241922291599368037113 36237931441718699526027835)
            ·
              refine ⟨54356897162578049289041753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36237931441718699526027835 54356897162578049289041753)
              ·
                refine ⟨40767672871933536966781315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54356897162578049289041753 40767672871933536966781315)
                ·
                  refine ⟨61151509307900305450171973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40767672871933536966781315 61151509307900305450171973)
                  ·
                    refine ⟨11465907995231307271907245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61151509307900305450171973 11465907995231307271907245)
                    ·
                      refine ⟨4299715498211740226965217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11465907995231307271907245 4299715498211740226965217)
                      ·
                        rfl

theorem cell23_8373666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_8373666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373666 prefixEnd_8373666 := by exact prefixLift 8373666
  have htrace : WordTrace (prefixWord ++ tailWord_8373666) baseStart_8373666 baseEnd_8373666 := by
    simpa [prefixWord, tailWord_8373666, baseEnd_8373666] using wordTrace_append hprefix tailTrace_8373666
  have hstable : (prefixWord ++ tailWord_8373666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373666).length < 2 ^ (prefixWord ++ tailWord_8373666).sum := by decide
  have hdescent : baseEnd_8373666 < baseStart_8373666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373696 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3]
def baseStart_8373696 : Nat := 118140960795 + 8373696 * 2 ^ 59
def prefixEnd_8373696 : Nat := 4983230072969 + 3 ^ 40 * 8373696 * 2
def baseEnd_8373696 : Nat := 4299730902631375109590079

theorem tailTrace_8373696 : CollatzResearch.WordTrace tailWord_8373696 prefixEnd_8373696 4299730902631375109590079 := by
  unfold tailWord_8373696
  simp only [CollatzResearch.WordTrace]
  refine ⟨152706891935768490132382471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203609189247691320176509961 152706891935768490132382471)
  ·
    refine ⟨229060337903652735198573707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152706891935768490132382471 229060337903652735198573707)
    ·
      refine ⟨343590506855479102797860561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229060337903652735198573707 343590506855479102797860561)
      ·
        refine ⟨257692880141609327098395421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343590506855479102797860561 257692880141609327098395421)
        ·
          refine ⟨96634830053103497661898283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257692880141609327098395421 96634830053103497661898283)
          ·
            refine ⟨144952245079655246492847425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96634830053103497661898283 144952245079655246492847425)
            ·
              refine ⟨108714183809741434869635569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144952245079655246492847425 108714183809741434869635569)
              ·
                refine ⟨81535637857306076152226677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108714183809741434869635569 81535637857306076152226677)
                ·
                  refine ⟨7643966049122444639271251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81535637857306076152226677 7643966049122444639271251)
                  ·
                    refine ⟨11465949073683666958906877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7643966049122444639271251 11465949073683666958906877)
                    ·
                      refine ⟨4299730902631375109590079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11465949073683666958906877 4299730902631375109590079)
                      ·
                        rfl

theorem cell23_8373696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_8373696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373696 prefixEnd_8373696 := by exact prefixLift 8373696
  have htrace : WordTrace (prefixWord ++ tailWord_8373696) baseStart_8373696 baseEnd_8373696 := by
    simpa [prefixWord, tailWord_8373696, baseEnd_8373696] using wordTrace_append hprefix tailTrace_8373696
  have hstable : (prefixWord ++ tailWord_8373696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373696).length < 2 ^ (prefixWord ++ tailWord_8373696).sum := by decide
  have hdescent : baseEnd_8373696 < baseStart_8373696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373733 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_8373733 : Nat := 118140960795 + 8373733 * 2 ^ 59
def prefixEnd_8373733 : Nat := 4983230072969 + 3 ^ 40 * 8373733 * 2
def baseEnd_8373733 : Nat := 1433249967138530488275803

theorem tailTrace_8373733 : CollatzResearch.WordTrace tailWord_8373733 prefixEnd_8373733 1433249967138530488275803 := by
  unfold tailWord_8373733
  simp only [CollatzResearch.WordTrace]
  refine ⟨305415133372402935583861853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203610088914935290389241235 305415133372402935583861853)
  ·
    refine ⟨114530675014651100843948195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305415133372402935583861853 114530675014651100843948195)
    ·
      refine ⟨171796012521976651265922293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114530675014651100843948195 171796012521976651265922293)
      ·
        refine ⟨16105876173935311056180215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171796012521976651265922293 16105876173935311056180215)
        ·
          refine ⟨24158814260902966584270323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105876173935311056180215 24158814260902966584270323)
          ·
            refine ⟨36238221391354449876405485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24158814260902966584270323 36238221391354449876405485)
            ·
              refine ⟨13589333021757918703652057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36238221391354449876405485 13589333021757918703652057)
              ·
                refine ⟨10191999766318439027739043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13589333021757918703652057 10191999766318439027739043)
                ·
                  refine ⟨15287999649477658541608565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191999766318439027739043 15287999649477658541608565)
                  ·
                    refine ⟨1433249967138530488275803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15287999649477658541608565 1433249967138530488275803)
                    ·
                      rfl

theorem cell23_8373733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_8373733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373733 prefixEnd_8373733 := by exact prefixLift 8373733
  have htrace : WordTrace (prefixWord ++ tailWord_8373733) baseStart_8373733 baseEnd_8373733 := by
    simpa [prefixWord, tailWord_8373733, baseEnd_8373733] using wordTrace_append hprefix tailTrace_8373733
  have hstable : (prefixWord ++ tailWord_8373733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373733).length < 2 ^ (prefixWord ++ tailWord_8373733).sum := by decide
  have hdescent : baseEnd_8373733 < baseStart_8373733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373736 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_8373736 : Nat := 118140960795 + 8373736 * 2 ^ 59
def prefixEnd_8373736 : Nat := 4983230072969 + 3 ^ 40 * 8373736 * 2
def baseEnd_8373736 : Nat := 4299751441857554953089895

theorem tailTrace_8373736 : CollatzResearch.WordTrace tailWord_8373736 prefixEnd_8373736 4299751441857554953089895 := by
  unfold tailWord_8373736
  simp only [CollatzResearch.WordTrace]
  refine ⟨152707621395696033548110531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203610161860928044730814041 152707621395696033548110531)
  ·
    refine ⟨229061432093544050322165797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152707621395696033548110531 229061432093544050322165797)
    ·
      refine ⟨42949018517539509435406087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229061432093544050322165797 42949018517539509435406087)
      ·
        refine ⟨64423527776309264153109131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42949018517539509435406087 64423527776309264153109131)
        ·
          refine ⟨96635291664463896229663697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64423527776309264153109131 96635291664463896229663697)
          ·
            refine ⟨72476468748347922172247773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96635291664463896229663697 72476468748347922172247773)
            ·
              refine ⟨27178675780630470814592915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72476468748347922172247773 27178675780630470814592915)
              ·
                refine ⟨40768013670945706221889373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27178675780630470814592915 40768013670945706221889373)
                ·
                  refine ⟨15288005126604639833208515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40768013670945706221889373 15288005126604639833208515)
                  ·
                    refine ⟨22932007689906959749812773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15288005126604639833208515 22932007689906959749812773)
                    ·
                      refine ⟨4299751441857554953089895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22932007689906959749812773 4299751441857554953089895)
                      ·
                        rfl

theorem cell23_8373736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_8373736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373736 prefixEnd_8373736 := by exact prefixLift 8373736
  have htrace : WordTrace (prefixWord ++ tailWord_8373736) baseStart_8373736 baseEnd_8373736 := by
    simpa [prefixWord, tailWord_8373736, baseEnd_8373736] using wordTrace_append hprefix tailTrace_8373736
  have hstable : (prefixWord ++ tailWord_8373736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373736).length < 2 ^ (prefixWord ++ tailWord_8373736).sum := by decide
  have hdescent : baseEnd_8373736 < baseStart_8373736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373746 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_8373746 : Nat := 118140960795 + 8373746 * 2 ^ 59
def prefixEnd_8373746 : Nat := 4983230072969 + 3 ^ 40 * 8373746 * 2
def baseEnd_8373746 : Nat := 1433252192221366637988283

theorem tailTrace_8373746 : CollatzResearch.WordTrace tailWord_8373746 prefixEnd_8373746 1433252192221366637988283 := by
  unfold tailWord_8373746
  simp only [CollatzResearch.WordTrace]
  refine ⟨76353901880338959701021273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203610405014237225869390061 76353901880338959701021273)
  ·
    refine ⟨57265426410254219775765955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76353901880338959701021273 57265426410254219775765955)
    ·
      refine ⟨85898139615381329663648933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57265426410254219775765955 85898139615381329663648933)
      ·
        refine ⟨16105901177883999311934175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85898139615381329663648933 16105901177883999311934175)
        ·
          refine ⟨24158851766825998967901263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105901177883999311934175 24158851766825998967901263)
          ·
            refine ⟨36238277650238998451851895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24158851766825998967901263 36238277650238998451851895)
            ·
              refine ⟨54357416475358497677777843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36238277650238998451851895 54357416475358497677777843)
              ·
                refine ⟨81536124713037746516666765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54357416475358497677777843 81536124713037746516666765)
                ·
                  refine ⟨30576046767389154943750037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81536124713037746516666765 30576046767389154943750037)
                  ·
                    refine ⟨1433252192221366637988283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30576046767389154943750037 1433252192221366637988283)
                    ·
                      rfl

theorem cell23_8373746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_8373746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373746 prefixEnd_8373746 := by exact prefixLift 8373746
  have htrace : WordTrace (prefixWord ++ tailWord_8373746) baseStart_8373746 baseEnd_8373746 := by
    simpa [prefixWord, tailWord_8373746, baseEnd_8373746] using wordTrace_append hprefix tailTrace_8373746
  have hstable : (prefixWord ++ tailWord_8373746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373746).length < 2 ^ (prefixWord ++ tailWord_8373746).sum := by decide
  have hdescent : baseEnd_8373746 < baseStart_8373746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373750 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_8373750 : Nat := 118140960795 + 8373750 * 2 ^ 59
def prefixEnd_8373750 : Nat := 4983230072969 + 3 ^ 40 * 8373750 * 2
def baseEnd_8373750 : Nat := 1433252876862239299438277

theorem tailTrace_8373750 : CollatzResearch.WordTrace tailWord_8373750 prefixEnd_8373750 1433252876862239299438277 := by
  unfold tailWord_8373750
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088484588333834217951919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203610502275560898324820469 19088484588333834217951919)
  ·
    refine ⟨28632726882500751326927879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088484588333834217951919 28632726882500751326927879)
    ·
      refine ⟨42949090323751126990391819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632726882500751326927879 42949090323751126990391819)
      ·
        refine ⟨64423635485626690485587729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42949090323751126990391819 64423635485626690485587729)
        ·
          refine ⟨48317726614220017864190797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64423635485626690485587729 48317726614220017864190797)
          ·
            refine ⟨18119147480332506699071549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48317726614220017864190797 18119147480332506699071549)
            ·
              refine ⟨6794680305124690012151831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18119147480332506699071549 6794680305124690012151831)
              ·
                refine ⟨10192020457687035018227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794680305124690012151831 10192020457687035018227747)
                ·
                  refine ⟨15288030686530552527341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192020457687035018227747 15288030686530552527341621)
                  ·
                    refine ⟨1433252876862239299438277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15288030686530552527341621 1433252876862239299438277)
                    ·
                      rfl

theorem cell23_8373750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_8373750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373750 prefixEnd_8373750 := by exact prefixLift 8373750
  have htrace : WordTrace (prefixWord ++ tailWord_8373750) baseStart_8373750 baseEnd_8373750 := by
    simpa [prefixWord, tailWord_8373750, baseEnd_8373750] using wordTrace_append hprefix tailTrace_8373750
  have hstable : (prefixWord ++ tailWord_8373750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373750).length < 2 ^ (prefixWord ++ tailWord_8373750).sum := by decide
  have hdescent : baseEnd_8373750 < baseStart_8373750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373756 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_8373756 : Nat := 118140960795 + 8373756 * 2 ^ 59
def prefixEnd_8373756 : Nat := 4983230072969 + 3 ^ 40 * 8373756 * 2
def baseEnd_8373756 : Nat := 4299761711470644874839803

theorem tailTrace_8373756 : CollatzResearch.WordTrace tailWord_8373756 prefixEnd_8373756 4299761711470644874839803 := by
  unfold tailWord_8373756
  simp only [CollatzResearch.WordTrace]
  refine ⟨152707986125659805255974561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203610648167546407007966081 152707986125659805255974561)
  ·
    refine ⟨114530989594244853941980921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152707986125659805255974561 114530989594244853941980921)
    ·
      refine ⟨85898242195683640456485691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114530989594244853941980921 85898242195683640456485691)
      ·
        refine ⟨128847363293525460684728537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85898242195683640456485691 128847363293525460684728537)
        ·
          refine ⟨96635522470144095513546403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128847363293525460684728537 96635522470144095513546403)
          ·
            refine ⟨144953283705216143270319605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96635522470144095513546403 144953283705216143270319605)
            ·
              refine ⟨13589370347364013431592463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144953283705216143270319605 13589370347364013431592463)
              ·
                refine ⟨20384055521046020147388695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589370347364013431592463 20384055521046020147388695)
                ·
                  refine ⟨30576083281569030221083043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20384055521046020147388695 30576083281569030221083043)
                  ·
                    refine ⟨45864124922353545331624565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30576083281569030221083043 45864124922353545331624565)
                    ·
                      refine ⟨4299761711470644874839803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45864124922353545331624565 4299761711470644874839803)
                      ·
                        rfl

theorem cell23_8373756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_8373756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373756 prefixEnd_8373756 := by exact prefixLift 8373756
  have htrace : WordTrace (prefixWord ++ tailWord_8373756) baseStart_8373756 baseEnd_8373756 := by
    simpa [prefixWord, tailWord_8373756, baseEnd_8373756] using wordTrace_append hprefix tailTrace_8373756
  have hstable : (prefixWord ++ tailWord_8373756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373756).length < 2 ^ (prefixWord ++ tailWord_8373756).sum := by decide
  have hdescent : baseEnd_8373756 < baseStart_8373756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373780 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_8373780 : Nat := 118140960795 + 8373780 * 2 ^ 59
def prefixEnd_8373780 : Nat := 4983230072969 + 3 ^ 40 * 8373780 * 2
def baseEnd_8373780 : Nat := 1433258011668784260313231

theorem tailTrace_8373780 : CollatzResearch.WordTrace tailWord_8373780 prefixEnd_8373780 1433258011668784260313231 := by
  unfold tailWord_8373780
  simp only [CollatzResearch.WordTrace]
  refine ⟨152708423801616331305411397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203611231735488441740548529 152708423801616331305411397)
  ·
    refine ⟨28632829462803062119764637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152708423801616331305411397 28632829462803062119764637)
    ·
      refine ⟨10737311048551148294911739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28632829462803062119764637 10737311048551148294911739)
      ·
        refine ⟨16105966572826722442367609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10737311048551148294911739 16105966572826722442367609)
        ·
          refine ⟨12079474929620041831775707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16105966572826722442367609 12079474929620041831775707)
          ·
            refine ⟨18119212394430062747663561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079474929620041831775707 18119212394430062747663561)
            ·
              refine ⟨13589409295822547060747671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18119212394430062747663561 13589409295822547060747671)
              ·
                refine ⟨20384113943733820591121507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589409295822547060747671 20384113943733820591121507)
                ·
                  refine ⟨30576170915600730886682261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20384113943733820591121507 30576170915600730886682261)
                  ·
                    refine ⟨1433258011668784260313231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30576170915600730886682261 1433258011668784260313231)
                    ·
                      rfl

theorem cell23_8373780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_8373780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373780 prefixEnd_8373780 := by exact prefixLift 8373780
  have htrace : WordTrace (prefixWord ++ tailWord_8373780) baseStart_8373780 baseEnd_8373780 := by
    simpa [prefixWord, tailWord_8373780, baseEnd_8373780] using wordTrace_append hprefix tailTrace_8373780
  have hstable : (prefixWord ++ tailWord_8373780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373780).length < 2 ^ (prefixWord ++ tailWord_8373780).sum := by decide
  have hdescent : baseEnd_8373780 < baseStart_8373780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373814 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_8373814 : Nat := 118140960795 + 8373814 * 2 ^ 59
def prefixEnd_8373814 : Nat := 4983230072969 + 3 ^ 40 * 8373814 * 2
def baseEnd_8373814 : Nat := 1433263831116201882638179

theorem tailTrace_8373814 : CollatzResearch.WordTrace tailWord_8373814 prefixEnd_8373814 1433263831116201882638179 := by
  unfold tailWord_8373814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088630480319342901097531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203612058456739657611706997 19088630480319342901097531)
  ·
    refine ⟨28632945720479014351646297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088630480319342901097531 28632945720479014351646297)
    ·
      refine ⟨21474709290359260763734723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28632945720479014351646297 21474709290359260763734723)
      ·
        refine ⟨32212063935538891145602085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21474709290359260763734723 32212063935538891145602085)
        ·
          refine ⟨6039761987913542089800391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32212063935538891145602085 6039761987913542089800391)
          ·
            refine ⟨9059642981870313134700587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039761987913542089800391 9059642981870313134700587)
            ·
              refine ⟨13589464472805469702050881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059642981870313134700587 13589464472805469702050881)
              ·
                refine ⟨10192098354604102276538161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13589464472805469702050881 10192098354604102276538161)
                ·
                  refine ⟨7644073765953076707403621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192098354604102276538161 7644073765953076707403621)
                  ·
                    refine ⟨1433263831116201882638179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644073765953076707403621 1433263831116201882638179)
                    ·
                      rfl

theorem cell23_8373814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_8373814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373814 prefixEnd_8373814 := by exact prefixLift 8373814
  have htrace : WordTrace (prefixWord ++ tailWord_8373814) baseStart_8373814 baseEnd_8373814 := by
    simpa [prefixWord, tailWord_8373814, baseEnd_8373814] using wordTrace_append hprefix tailTrace_8373814
  have hstable : (prefixWord ++ tailWord_8373814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373814).length < 2 ^ (prefixWord ++ tailWord_8373814).sum := by decide
  have hdescent : baseEnd_8373814 < baseStart_8373814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373820 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_8373820 : Nat := 118140960795 + 8373820 * 2 ^ 59
def prefixEnd_8373820 : Nat := 4983230072969 + 3 ^ 40 * 8373820 * 2
def baseEnd_8373820 : Nat := 4299794574232532624439509

theorem tailTrace_8373820 : CollatzResearch.WordTrace tailWord_8373820 prefixEnd_8373820 4299794574232532624439509 := by
  unfold tailWord_8373820
  simp only [CollatzResearch.WordTrace]
  refine ⟨152709153261543874721139457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203612204348725166294852609 152709153261543874721139457)
  ·
    refine ⟨114531864946157906040854593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152709153261543874721139457 114531864946157906040854593)
    ·
      refine ⟨85898898709618429530640945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114531864946157906040854593 85898898709618429530640945)
      ·
        refine ⟨64424174032213822147980709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85898898709618429530640945 64424174032213822147980709)
        ·
          refine ⟨12079532631040091652746383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64424174032213822147980709 12079532631040091652746383)
          ·
            refine ⟨18119298946560137479119575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079532631040091652746383 18119298946560137479119575)
            ·
              refine ⟨27178948419840206218679363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18119298946560137479119575 27178948419840206218679363)
              ·
                refine ⟨40768422629760309328019045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27178948419840206218679363 40768422629760309328019045)
                ·
                  refine ⟨7644079243080057999003571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40768422629760309328019045 7644079243080057999003571)
                  ·
                    refine ⟨11466118864620086998505357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7644079243080057999003571 11466118864620086998505357)
                    ·
                      refine ⟨4299794574232532624439509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466118864620086998505357 4299794574232532624439509)
                      ·
                        rfl

theorem cell23_8373820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_8373820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373820 prefixEnd_8373820 := by exact prefixLift 8373820
  have htrace : WordTrace (prefixWord ++ tailWord_8373820) baseStart_8373820 baseEnd_8373820 := by
    simpa [prefixWord, tailWord_8373820, baseEnd_8373820] using wordTrace_append hprefix tailTrace_8373820
  have hstable : (prefixWord ++ tailWord_8373820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373820).length < 2 ^ (prefixWord ++ tailWord_8373820).sum := by decide
  have hdescent : baseEnd_8373820 < baseStart_8373820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373836 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_8373836 : Nat := 118140960795 + 8373836 * 2 ^ 59
def prefixEnd_8373836 : Nat := 4983230072969 + 3 ^ 40 * 8373836 * 2
def baseEnd_8373836 : Nat := 1433267596641001520613145

theorem tailTrace_8373836 : CollatzResearch.WordTrace tailWord_8373836 prefixEnd_8373836 1433267596641001520613145 := by
  unfold tailWord_8373836
  simp only [CollatzResearch.WordTrace]
  refine ⟨152709445045514892087430681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203612593394019856116574241 152709445045514892087430681)
  ·
    refine ⟨114532083784136169065573011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152709445045514892087430681 114532083784136169065573011)
    ·
      refine ⟨171798125676204253598359517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114532083784136169065573011 171798125676204253598359517)
      ·
        refine ⟨64424297128576595099384819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171798125676204253598359517 64424297128576595099384819)
        ·
          refine ⟨96636445692864892649077229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64424297128576595099384819 96636445692864892649077229)
          ·
            refine ⟨36238667134824334743403961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96636445692864892649077229 36238667134824334743403961)
            ·
              refine ⟨27179000351118251057552971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36238667134824334743403961 27179000351118251057552971)
              ·
                refine ⟨40768500526677376586329457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27179000351118251057552971 40768500526677376586329457)
                ·
                  refine ⟨30576375395008032439747093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40768500526677376586329457 30576375395008032439747093)
                  ·
                    refine ⟨1433267596641001520613145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30576375395008032439747093 1433267596641001520613145)
                    ·
                      rfl

theorem cell23_8373836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_8373836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373836 prefixEnd_8373836 := by exact prefixLift 8373836
  have htrace : WordTrace (prefixWord ++ tailWord_8373836) baseStart_8373836 baseEnd_8373836 := by
    simpa [prefixWord, tailWord_8373836, baseEnd_8373836] using wordTrace_append hprefix tailTrace_8373836
  have hstable : (prefixWord ++ tailWord_8373836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373836).length < 2 ^ (prefixWord ++ tailWord_8373836).sum := by decide
  have hdescent : baseEnd_8373836 < baseStart_8373836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373837 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_8373837 : Nat := 118140960795 + 8373837 * 2 ^ 59
def prefixEnd_8373837 : Nat := 4983230072969 + 3 ^ 40 * 8373837 * 2
def baseEnd_8373837 : Nat := 4299803303403659057926931

theorem tailTrace_8373837 : CollatzResearch.WordTrace tailWord_8373837 prefixEnd_8373837 4299803303403659057926931 := by
  unfold tailWord_8373837
  simp only [CollatzResearch.WordTrace]
  refine ⟨305418926564026161345647765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203612617709350774230431843 305418926564026161345647765)
  ·
    refine ⟨14316512182688726313077239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305418926564026161345647765 14316512182688726313077239)
    ·
      refine ⟨21474768274033089469615859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14316512182688726313077239 21474768274033089469615859)
      ·
        refine ⟨32212152411049634204423789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21474768274033089469615859 32212152411049634204423789)
        ·
          refine ⟨12079557154143612826658921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32212152411049634204423789 12079557154143612826658921)
          ·
            refine ⟨9059667865607709619994191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12079557154143612826658921 9059667865607709619994191)
            ·
              refine ⟨13589501798411564429991287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059667865607709619994191 13589501798411564429991287)
              ·
                refine ⟨20384252697617346644986931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13589501798411564429991287 20384252697617346644986931)
                ·
                  refine ⟨30576379046426019967480397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20384252697617346644986931 30576379046426019967480397)
                  ·
                    refine ⟨11466142142409757487805149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30576379046426019967480397 11466142142409757487805149)
                    ·
                      refine ⟨4299803303403659057926931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466142142409757487805149 4299803303403659057926931)
                      ·
                        rfl

theorem cell23_8373837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_8373837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373837 prefixEnd_8373837 := by exact prefixLift 8373837
  have htrace : WordTrace (prefixWord ++ tailWord_8373837) baseStart_8373837 baseEnd_8373837 := by
    simpa [prefixWord, tailWord_8373837, baseEnd_8373837] using wordTrace_append hprefix tailTrace_8373837
  have hstable : (prefixWord ++ tailWord_8373837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373837).length < 2 ^ (prefixWord ++ tailWord_8373837).sum := by decide
  have hdescent : baseEnd_8373837 < baseStart_8373837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373860 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_8373860 : Nat := 118140960795 + 8373860 * 2 ^ 59
def prefixEnd_8373860 : Nat := 4983230072969 + 3 ^ 40 * 8373860 * 2
def baseEnd_8373860 : Nat := 4299815113458712467939325

theorem tailTrace_8373860 : CollatzResearch.WordTrace tailWord_8373860 prefixEnd_8373860 4299815113458712467939325 := by
  unfold tailWord_8373860
  simp only [CollatzResearch.WordTrace]
  refine ⟨152709882721471418136867517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203613176961961890849156689 152709882721471418136867517)
  ·
    refine ⟨57266206020551781801325319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152709882721471418136867517 57266206020551781801325319)
    ·
      refine ⟨85899309030827672701987979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57266206020551781801325319 85899309030827672701987979)
      ·
        refine ⟨128848963546241509052981969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85899309030827672701987979 128848963546241509052981969)
        ·
          refine ⟨96636722659681131789736477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128848963546241509052981969 96636722659681131789736477)
          ·
            refine ⟨36238770997380424421151179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96636722659681131789736477 36238770997380424421151179)
            ·
              refine ⟨54358156496070636631726769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36238770997380424421151179 54358156496070636631726769)
              ·
                refine ⟨40768617372052977473795077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54358156496070636631726769 40768617372052977473795077)
                ·
                  refine ⟨7644115757259933276336577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40768617372052977473795077 7644115757259933276336577)
                  ·
                    refine ⟨5733086817944949957252433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644115757259933276336577 5733086817944949957252433)
                    ·
                      refine ⟨4299815113458712467939325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733086817944949957252433 4299815113458712467939325)
                      ·
                        rfl

theorem cell23_8373860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_8373860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373860 prefixEnd_8373860 := by exact prefixLift 8373860
  have htrace : WordTrace (prefixWord ++ tailWord_8373860) baseStart_8373860 baseEnd_8373860 := by
    simpa [prefixWord, tailWord_8373860, baseEnd_8373860] using wordTrace_append hprefix tailTrace_8373860
  have hstable : (prefixWord ++ tailWord_8373860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373860).length < 2 ^ (prefixWord ++ tailWord_8373860).sum := by decide
  have hdescent : baseEnd_8373860 < baseStart_8373860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373877 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8373877 : Nat := 118140960795 + 8373877 * 2 ^ 59
def prefixEnd_8373877 : Nat := 4983230072969 + 3 ^ 40 * 8373877 * 2
def baseEnd_8373877 : Nat := 4299823842629838901426747

theorem tailTrace_8373877 : CollatzResearch.WordTrace tailWord_8373877 prefixEnd_8373877 4299823842629838901426747 := by
  unfold tailWord_8373877
  simp only [CollatzResearch.WordTrace]
  refine ⟨305420385483881248177103885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203613590322587498784735923 305420385483881248177103885)
  ·
    refine ⟨114532644556455468066413957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305420385483881248177103885 114532644556455468066413957)
    ·
      refine ⟨21474870854335400262452617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114532644556455468066413957 21474870854335400262452617)
      ·
        refine ⟨16106153140751550196839463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21474870854335400262452617 16106153140751550196839463)
        ·
          refine ⟨24159229711127325295259195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16106153140751550196839463 24159229711127325295259195)
          ·
            refine ⟨36238844566690987942888793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24159229711127325295259195 36238844566690987942888793)
            ·
              refine ⟨27179133425018240957166595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36238844566690987942888793 27179133425018240957166595)
              ·
                refine ⟨40768700137527361435749893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27179133425018240957166595 40768700137527361435749893)
                ·
                  refine ⟨7644131275786380269203105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40768700137527361435749893 7644131275786380269203105)
                  ·
                    refine ⟨5733098456839785201902329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644131275786380269203105 5733098456839785201902329)
                    ·
                      refine ⟨4299823842629838901426747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733098456839785201902329 4299823842629838901426747)
                      ·
                        rfl

theorem cell23_8373877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8373877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373877 prefixEnd_8373877 := by exact prefixLift 8373877
  have htrace : WordTrace (prefixWord ++ tailWord_8373877) baseStart_8373877 baseEnd_8373877 := by
    simpa [prefixWord, tailWord_8373877, baseEnd_8373877] using wordTrace_append hprefix tailTrace_8373877
  have hstable : (prefixWord ++ tailWord_8373877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373877).length < 2 ^ (prefixWord ++ tailWord_8373877).sum := by decide
  have hdescent : baseEnd_8373877 < baseStart_8373877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373928 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_8373928 : Nat := 118140960795 + 8373928 * 2 ^ 59
def prefixEnd_8373928 : Nat := 4983230072969 + 3 ^ 40 * 8373928 * 2
def baseEnd_8373928 : Nat := 4299850030143218201889013

theorem tailTrace_8373928 : CollatzResearch.WordTrace tailWord_8373928 prefixEnd_8373928 4299850030143218201889013 := by
  unfold tailWord_8373928
  simp only [CollatzResearch.WordTrace]
  refine ⟨152711122803348241943605219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203614830404464322591473625 152711122803348241943605219)
  ·
    refine ⟨229066684205022362915407829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152711122803348241943605219 229066684205022362915407829)
    ·
      refine ⟨5368750411055211630829871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 229066684205022362915407829 5368750411055211630829871)
      ·
        refine ⟨8053125616582817446244807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368750411055211630829871 8053125616582817446244807)
        ·
          refine ⟨12079688424874226169367211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053125616582817446244807 12079688424874226169367211)
          ·
            refine ⟨18119532637311339254050817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079688424874226169367211 18119532637311339254050817)
            ·
              refine ⟨13589649477983504440538113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18119532637311339254050817 13589649477983504440538113)
              ·
                refine ⟨10192237108487628330403585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13589649477983504440538113 10192237108487628330403585)
                ·
                  refine ⟨7644177831365721247802689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192237108487628330403585 7644177831365721247802689)
                  ·
                    refine ⟨5733133373524290935852017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644177831365721247802689 5733133373524290935852017)
                    ·
                      refine ⟨4299850030143218201889013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733133373524290935852017 4299850030143218201889013)
                      ·
                        rfl

theorem cell23_8373928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_8373928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373928 prefixEnd_8373928 := by exact prefixLift 8373928
  have htrace : WordTrace (prefixWord ++ tailWord_8373928) baseStart_8373928 baseEnd_8373928 := by
    simpa [prefixWord, tailWord_8373928, baseEnd_8373928] using wordTrace_append hprefix tailTrace_8373928
  have hstable : (prefixWord ++ tailWord_8373928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373928).length < 2 ^ (prefixWord ++ tailWord_8373928).sum := by decide
  have hdescent : baseEnd_8373928 < baseStart_8373928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373950 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_8373950 : Nat := 118140960795 + 8373950 * 2 ^ 59
def prefixEnd_8373950 : Nat := 4983230072969 + 3 ^ 40 * 8373950 * 2
def baseEnd_8373950 : Nat := 4299861326717617115813911

theorem tailTrace_8373950 : CollatzResearch.WordTrace tailWord_8373950 prefixEnd_8373950 4299861326717617115813911 := by
  unfold tailWord_8373950
  simp only [CollatzResearch.WordTrace]
  refine ⟨38177881001577097705563913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203615365341744521096340869 38177881001577097705563913)
  ·
    refine ⟨28633410751182823279172935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38177881001577097705563913 28633410751182823279172935)
    ·
      refine ⟨42950116126774234918759403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633410751182823279172935 42950116126774234918759403)
      ·
        refine ⟨64425174190161352378139105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42950116126774234918759403 64425174190161352378139105)
        ·
          refine ⟨48318880642621014283604329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64425174190161352378139105 48318880642621014283604329)
          ·
            refine ⟨36239160481965760712703247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48318880642621014283604329 36239160481965760712703247)
            ·
              refine ⟨54358740722948641069054871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36239160481965760712703247 54358740722948641069054871)
              ·
                refine ⟨81538111084422961603582307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54358740722948641069054871 81538111084422961603582307)
                ·
                  refine ⟨122307166626634442405373461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81538111084422961603582307 122307166626634442405373461)
                  ·
                    refine ⟨5733148435623489487751881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122307166626634442405373461 5733148435623489487751881)
                    ·
                      refine ⟨4299861326717617115813911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733148435623489487751881 4299861326717617115813911)
                      ·
                        rfl

theorem cell23_8373950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_8373950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373950 prefixEnd_8373950 := by exact prefixLift 8373950
  have htrace : WordTrace (prefixWord ++ tailWord_8373950) baseStart_8373950 baseEnd_8373950 := by
    simpa [prefixWord, tailWord_8373950, baseEnd_8373950] using wordTrace_append hprefix tailTrace_8373950
  have hstable : (prefixWord ++ tailWord_8373950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373950).length < 2 ^ (prefixWord ++ tailWord_8373950).sum := by decide
  have hdescent : baseEnd_8373950 < baseStart_8373950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373970 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_8373970 : Nat := 118140960795 + 8373970 * 2 ^ 59
def prefixEnd_8373970 : Nat := 4983230072969 + 3 ^ 40 * 8373970 * 2
def baseEnd_8373970 : Nat := 4299871596330707037563819

theorem tailTrace_8373970 : CollatzResearch.WordTrace tailWord_8373970 prefixEnd_8373970 4299871596330707037563819 := by
  unfold tailWord_8373970
  simp only [CollatzResearch.WordTrace]
  refine ⟨76355944368136081265059841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203615851648362883373492909 76355944368136081265059841)
  ·
    refine ⟨57266958276102060948794881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76355944368136081265059841 57266958276102060948794881)
    ·
      refine ⟨42950218707076545711596161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57266958276102060948794881 42950218707076545711596161)
      ·
        refine ⟨32212664030307409283697121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42950218707076545711596161 32212664030307409283697121)
        ·
          refine ⟨24159498022730556962772841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32212664030307409283697121 24159498022730556962772841)
          ·
            refine ⟨18119623517047917722079631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24159498022730556962772841 18119623517047917722079631)
            ·
              refine ⟨27179435275571876583119447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18119623517047917722079631 27179435275571876583119447)
              ·
                refine ⟨40769152913357814874679171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27179435275571876583119447 40769152913357814874679171)
                ·
                  refine ⟨61153729370036722312018757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40769152913357814874679171 61153729370036722312018757)
                  ·
                    refine ⟨11466324256881885433503517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61153729370036722312018757 11466324256881885433503517)
                    ·
                      refine ⟨4299871596330707037563819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466324256881885433503517 4299871596330707037563819)
                      ·
                        rfl

theorem cell23_8373970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_8373970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373970 prefixEnd_8373970 := by exact prefixLift 8373970
  have htrace : WordTrace (prefixWord ++ tailWord_8373970) baseStart_8373970 baseEnd_8373970 := by
    simpa [prefixWord, tailWord_8373970, baseEnd_8373970] using wordTrace_append hprefix tailTrace_8373970
  have hstable : (prefixWord ++ tailWord_8373970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373970).length < 2 ^ (prefixWord ++ tailWord_8373970).sum := by decide
  have hdescent : baseEnd_8373970 < baseStart_8373970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8373977 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 1, 4]
def baseStart_8373977 : Nat := 118140960795 + 8373977 * 2 ^ 59
def prefixEnd_8373977 : Nat := 4983230072969 + 3 ^ 40 * 8373977 * 2
def baseEnd_8373977 : Nat := 1433291730231762836725429

theorem tailTrace_8373977 : CollatzResearch.WordTrace tailWord_8373977 prefixEnd_8373977 1433291730231762836725429 := by
  unfold tailWord_8373977
  simp only [CollatzResearch.WordTrace]
  refine ⟨305424032783518965255744185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203616021855679310170496123 305424032783518965255744185)
  ·
    refine ⟨229068024587639223941808139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305424032783518965255744185 229068024587639223941808139)
    ·
      refine ⟨343602036881458835912712209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229068024587639223941808139 343602036881458835912712209)
      ·
        refine ⟨257701527661094126934534157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343602036881458835912712209 257701527661094126934534157)
        ·
          refine ⟨96638072872910297600450309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257701527661094126934534157 96638072872910297600450309)
          ·
            refine ⟨18119638663670680800084433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96638072872910297600450309 18119638663670680800084433)
            ·
              refine ⟨13589728997753010600063325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18119638663670680800084433 13589728997753010600063325)
              ·
                refine ⟨5096148374157378975023747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13589728997753010600063325 5096148374157378975023747)
                ·
                  refine ⟨7644222561236068462535621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096148374157378975023747 7644222561236068462535621)
                  ·
                    refine ⟨1433291730231762836725429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644222561236068462535621 1433291730231762836725429)
                    ·
                      rfl

theorem cell23_8373977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 4].length) (baseStart_8373977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8373977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8373977 prefixEnd_8373977 := by exact prefixLift 8373977
  have htrace : WordTrace (prefixWord ++ tailWord_8373977) baseStart_8373977 baseEnd_8373977 := by
    simpa [prefixWord, tailWord_8373977, baseEnd_8373977] using wordTrace_append hprefix tailTrace_8373977
  have hstable : (prefixWord ++ tailWord_8373977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8373977).length < 2 ^ (prefixWord ++ tailWord_8373977).sum := by decide
  have hdescent : baseEnd_8373977 < baseStart_8373977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8373977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374020 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_8374020 : Nat := 118140960795 + 8374020 * 2 ^ 59
def prefixEnd_8374020 : Nat := 4983230072969 + 3 ^ 40 * 8374020 * 2
def baseEnd_8374020 : Nat := 1433299090121143947312863

theorem tailTrace_8374020 : CollatzResearch.WordTrace tailWord_8374020 prefixEnd_8374020 1433299090121143947312863 := by
  unfold tailWord_8374020
  simp only [CollatzResearch.WordTrace]
  refine ⟨152712800561181591799779757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203617067414908789066373009 152712800561181591799779757)
  ·
    refine ⟨57267300210443096924917409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152712800561181591799779757 57267300210443096924917409)
    ·
      refine ⟨42950475157832322693688057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57267300210443096924917409 42950475157832322693688057)
      ·
        refine ⟨32212856368374242020266043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42950475157832322693688057 32212856368374242020266043)
        ·
          refine ⟨48319284552561363030399065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32212856368374242020266043 48319284552561363030399065)
          ·
            refine ⟨36239463414421022272799299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48319284552561363030399065 36239463414421022272799299)
            ·
              refine ⟨54359195121631533409198949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36239463414421022272799299 54359195121631533409198949)
              ·
                refine ⟨10192349085305912514224803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54359195121631533409198949 10192349085305912514224803)
                ·
                  refine ⟨15288523627958868771337205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192349085305912514224803 15288523627958868771337205)
                  ·
                    refine ⟨1433299090121143947312863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15288523627958868771337205 1433299090121143947312863)
                    ·
                      rfl

theorem cell23_8374020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_8374020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374020 prefixEnd_8374020 := by exact prefixLift 8374020
  have htrace : WordTrace (prefixWord ++ tailWord_8374020) baseStart_8374020 baseEnd_8374020 := by
    simpa [prefixWord, tailWord_8374020, baseEnd_8374020] using wordTrace_append hprefix tailTrace_8374020
  have hstable : (prefixWord ++ tailWord_8374020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374020).length < 2 ^ (prefixWord ++ tailWord_8374020).sum := by decide
  have hdescent : baseEnd_8374020 < baseStart_8374020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374040 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_8374040 : Nat := 118140960795 + 8374040 * 2 ^ 59
def prefixEnd_8374040 : Nat := 4983230072969 + 3 ^ 40 * 8374040 * 2
def baseEnd_8374040 : Nat := 4299907539976521763688497

theorem tailTrace_8374040 : CollatzResearch.WordTrace tailWord_8374040 prefixEnd_8374040 4299907539976521763688497 := by
  unfold tailWord_8374040
  simp only [CollatzResearch.WordTrace]
  refine ⟨152713165291145363507643787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203617553721527151343525049 152713165291145363507643787)
  ·
    refine ⟨229069747936718045261465681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152713165291145363507643787 229069747936718045261465681)
    ·
      refine ⟨171802310952538533946099261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229069747936718045261465681 171802310952538533946099261)
      ·
        refine ⟨64425866607201950229787223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171802310952538533946099261 64425866607201950229787223)
        ·
          refine ⟨96638799910802925344680835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64425866607201950229787223 96638799910802925344680835)
          ·
            refine ⟨144958199866204388017021253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96638799910802925344680835 144958199866204388017021253)
            ·
              refine ⟨27179662474913322753191485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144958199866204388017021253 27179662474913322753191485)
              ·
                refine ⟨10192373428092496032446807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27179662474913322753191485 10192373428092496032446807)
                ·
                  refine ⟨15288560142138744048670211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192373428092496032446807 15288560142138744048670211)
                  ·
                    refine ⟨22932840213208116073005317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15288560142138744048670211 22932840213208116073005317)
                    ·
                      refine ⟨4299907539976521763688497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22932840213208116073005317 4299907539976521763688497)
                      ·
                        rfl

theorem cell23_8374040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_8374040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374040 prefixEnd_8374040 := by exact prefixLift 8374040
  have htrace : WordTrace (prefixWord ++ tailWord_8374040) baseStart_8374040 baseEnd_8374040 := by
    simpa [prefixWord, tailWord_8374040, baseEnd_8374040] using wordTrace_append hprefix tailTrace_8374040
  have hstable : (prefixWord ++ tailWord_8374040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374040).length < 2 ^ (prefixWord ++ tailWord_8374040).sum := by decide
  have hdescent : baseEnd_8374040 < baseStart_8374040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374050 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_8374050 : Nat := 118140960795 + 8374050 * 2 ^ 59
def prefixEnd_8374050 : Nat := 4983230072969 + 3 ^ 40 * 8374050 * 2
def baseEnd_8374050 : Nat := 1433304224927688908187817

theorem tailTrace_8374050 : CollatzResearch.WordTrace tailWord_8374050 prefixEnd_8374050 1433304224927688908187817 := by
  unfold tailWord_8374050
  simp only [CollatzResearch.WordTrace]
  refine ⟨76356673828063624680787901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203617796874836332482101069 76356673828063624680787901)
  ·
    refine ⟨28633752685523859255295463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76356673828063624680787901 28633752685523859255295463)
    ·
      refine ⟨42950629028285788882943195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633752685523859255295463 42950629028285788882943195)
      ·
        refine ⟨64425943542428683324414793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42950629028285788882943195 64425943542428683324414793)
        ·
          refine ⟨48319457656821512493311095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64425943542428683324414793 48319457656821512493311095)
          ·
            refine ⟨72479186485232268739966643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48319457656821512493311095 72479186485232268739966643)
            ·
              refine ⟨108718779727848403109949965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72479186485232268739966643 108718779727848403109949965)
              ·
                refine ⟨40769542397943151166231237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108718779727848403109949965 40769542397943151166231237)
                ·
                  refine ⟨7644289199614340843668357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40769542397943151166231237 7644289199614340843668357)
                  ·
                    refine ⟨1433304224927688908187817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644289199614340843668357 1433304224927688908187817)
                    ·
                      rfl

theorem cell23_8374050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_8374050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374050 prefixEnd_8374050 := by exact prefixLift 8374050
  have htrace : WordTrace (prefixWord ++ tailWord_8374050) baseStart_8374050 baseEnd_8374050 := by
    simpa [prefixWord, tailWord_8374050, baseEnd_8374050] using wordTrace_append hprefix tailTrace_8374050
  have hstable : (prefixWord ++ tailWord_8374050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374050).length < 2 ^ (prefixWord ++ tailWord_8374050).sum := by decide
  have hdescent : baseEnd_8374050 < baseStart_8374050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374053 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_8374053 : Nat := 118140960795 + 8374053 * 2 ^ 59
def prefixEnd_8374053 : Nat := 4983230072969 + 3 ^ 40 * 8374053 * 2
def baseEnd_8374053 : Nat := 4299914215225030212825937

theorem tailTrace_8374053 : CollatzResearch.WordTrace tailWord_8374053 prefixEnd_8374053 4299914215225030212825937 := by
  unfold tailWord_8374053
  simp only [CollatzResearch.WordTrace]
  refine ⟨305426804731243630235510813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203617869820829086823673875 305426804731243630235510813)
  ·
    refine ⟨114535051774216361338316555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305426804731243630235510813 114535051774216361338316555)
    ·
      refine ⟨171802577661324542007474833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114535051774216361338316555 171802577661324542007474833)
      ·
        refine ⟨128851933245993406505606125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171802577661324542007474833 128851933245993406505606125)
        ·
          refine ⟨48319474967247527439602297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128851933245993406505606125 48319474967247527439602297)
          ·
            refine ⟨36239606225435645579701723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48319474967247527439602297 36239606225435645579701723)
            ·
              refine ⟨54359409338153468369552585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36239606225435645579701723 54359409338153468369552585)
              ·
                refine ⟨40769557003615101277164439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54359409338153468369552585 40769557003615101277164439)
                ·
                  refine ⟨61154335505422651915746659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40769557003615101277164439 61154335505422651915746659)
                  ·
                    refine ⟨91731503258133977873619989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61154335505422651915746659 91731503258133977873619989)
                    ·
                      refine ⟨4299914215225030212825937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91731503258133977873619989 4299914215225030212825937)
                      ·
                        rfl

theorem cell23_8374053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_8374053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374053 prefixEnd_8374053 := by exact prefixLift 8374053
  have htrace : WordTrace (prefixWord ++ tailWord_8374053) baseStart_8374053 baseEnd_8374053 := by
    simpa [prefixWord, tailWord_8374053, baseEnd_8374053] using wordTrace_append hprefix tailTrace_8374053
  have hstable : (prefixWord ++ tailWord_8374053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374053).length < 2 ^ (prefixWord ++ tailWord_8374053).sum := by decide
  have hdescent : baseEnd_8374053 < baseStart_8374053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374067 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 2, 4]
def baseStart_8374067 : Nat := 118140960795 + 8374067 * 2 ^ 59
def prefixEnd_8374067 : Nat := 4983230072969 + 3 ^ 40 * 8374067 * 2
def baseEnd_8374067 : Nat := 1433307134651397719350291

theorem tailTrace_8374067 : CollatzResearch.WordTrace tailWord_8374067 prefixEnd_8374067 1433307134651397719350291 := by
  unfold tailWord_8374067
  simp only [CollatzResearch.WordTrace]
  refine ⟨305427315353192910626520455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203618210235461940417680303 305427315353192910626520455)
  ·
    refine ⟨458140973029789365939780683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305427315353192910626520455 458140973029789365939780683)
    ·
      refine ⟨687211459544684048909671025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458140973029789365939780683 687211459544684048909671025)
      ·
        refine ⟨515408594658513036682253269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687211459544684048909671025 515408594658513036682253269)
        ·
          refine ⟨12079888937308899297240311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 515408594658513036682253269 12079888937308899297240311)
          ·
            refine ⟨18119833405963348945860467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079888937308899297240311 18119833405963348945860467)
            ·
              refine ⟨27179750108945023418790701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18119833405963348945860467 27179750108945023418790701)
              ·
                refine ⟨10192406290854383782046513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27179750108945023418790701 10192406290854383782046513)
                ·
                  refine ⟨7644304718140787836534885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192406290854383782046513 7644304718140787836534885)
                  ·
                    refine ⟨1433307134651397719350291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644304718140787836534885 1433307134651397719350291)
                    ·
                      rfl

theorem cell23_8374067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 4].length) (baseStart_8374067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374067 prefixEnd_8374067 := by exact prefixLift 8374067
  have htrace : WordTrace (prefixWord ++ tailWord_8374067) baseStart_8374067 baseEnd_8374067 := by
    simpa [prefixWord, tailWord_8374067, baseEnd_8374067] using wordTrace_append hprefix tailTrace_8374067
  have hstable : (prefixWord ++ tailWord_8374067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374067).length < 2 ^ (prefixWord ++ tailWord_8374067).sum := by decide
  have hdescent : baseEnd_8374067 < baseStart_8374067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374077 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_8374077 : Nat := 118140960795 + 8374077 * 2 ^ 59
def prefixEnd_8374077 : Nat := 4983230072969 + 3 ^ 40 * 8374077 * 2
def baseEnd_8374077 : Nat := 4299926538760738118925827

theorem tailTrace_8374077 : CollatzResearch.WordTrace tailWord_8374077 prefixEnd_8374077 4299926538760738118925827 := by
  unfold tailWord_8374077
  simp only [CollatzResearch.WordTrace]
  refine ⟨305427680083156682334384485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203618453388771121556256323 305427680083156682334384485)
  ·
    refine ⟨57267690015591877937697091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305427680083156682334384485 57267690015591877937697091)
    ·
      refine ⟨85901535023387816906545637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57267690015591877937697091 85901535023387816906545637)
      ·
        refine ⟨16106537816885215669977307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85901535023387816906545637 16106537816885215669977307)
        ·
          refine ⟨24159806725327823504965961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16106537816885215669977307 24159806725327823504965961)
          ·
            refine ⟨18119855043995867628724471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24159806725327823504965961 18119855043995867628724471)
            ·
              refine ⟨27179782565993801443086707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18119855043995867628724471 27179782565993801443086707)
              ·
                refine ⟨40769673848990702164630061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27179782565993801443086707 40769673848990702164630061)
                ·
                  refine ⟨15288627693371513311736273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40769673848990702164630061 15288627693371513311736273)
                  ·
                    refine ⟨11466470770028634983802205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15288627693371513311736273 11466470770028634983802205)
                    ·
                      refine ⟨4299926538760738118925827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466470770028634983802205 4299926538760738118925827)
                      ·
                        rfl

theorem cell23_8374077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_8374077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374077 prefixEnd_8374077 := by exact prefixLift 8374077
  have htrace : WordTrace (prefixWord ++ tailWord_8374077) baseStart_8374077 baseEnd_8374077 := by
    simpa [prefixWord, tailWord_8374077, baseEnd_8374077] using wordTrace_append hprefix tailTrace_8374077
  have hstable : (prefixWord ++ tailWord_8374077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374077).length < 2 ^ (prefixWord ++ tailWord_8374077).sum := by decide
  have hdescent : baseEnd_8374077 < baseStart_8374077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374090 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_8374090 : Nat := 118140960795 + 8374090 * 2 ^ 59
def prefixEnd_8374090 : Nat := 4983230072969 + 3 ^ 40 * 8374090 * 2
def baseEnd_8374090 : Nat := 4299933214009246568063267

theorem tailTrace_8374090 : CollatzResearch.WordTrace tailWord_8374090 prefixEnd_8374090 4299933214009246568063267 := by
  unfold tailWord_8374090
  simp only [CollatzResearch.WordTrace]
  refine ⟨76357038558027396388651931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203618769488073057036405149 76357038558027396388651931)
  ·
    refine ⟨114535557837041094582977897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76357038558027396388651931 114535557837041094582977897)
    ·
      refine ⟨85901668377780820937233423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114535557837041094582977897 85901668377780820937233423)
      ·
        refine ⟨128852502566671231405850135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85901668377780820937233423 128852502566671231405850135)
        ·
          refine ⟨193278753850006847108775203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128852502566671231405850135 193278753850006847108775203)
          ·
            refine ⟨289918130775010270663162805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193278753850006847108775203 289918130775010270663162805)
            ·
              refine ⟨27179824760157212874671513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289918130775010270663162805 27179824760157212874671513)
              ·
                refine ⟨20384868570117909656003635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27179824760157212874671513 20384868570117909656003635)
                ·
                  refine ⟨30577302855176864484005453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20384868570117909656003635 30577302855176864484005453)
                  ·
                    refine ⟨11466488570691324181502045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30577302855176864484005453 11466488570691324181502045)
                    ·
                      refine ⟨4299933214009246568063267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466488570691324181502045 4299933214009246568063267)
                      ·
                        rfl

theorem cell23_8374090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_8374090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374090 prefixEnd_8374090 := by exact prefixLift 8374090
  have htrace : WordTrace (prefixWord ++ tailWord_8374090) baseStart_8374090 baseEnd_8374090 := by
    simpa [prefixWord, tailWord_8374090, baseEnd_8374090] using wordTrace_append hprefix tailTrace_8374090
  have hstable : (prefixWord ++ tailWord_8374090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374090).length < 2 ^ (prefixWord ++ tailWord_8374090).sum := by decide
  have hdescent : baseEnd_8374090 < baseStart_8374090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374108 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_8374108 : Nat := 118140960795 + 8374108 * 2 ^ 59
def prefixEnd_8374108 : Nat := 4983230072969 + 3 ^ 40 * 8374108 * 2
def baseEnd_8374108 : Nat := 4299942456661027497638185

theorem tailTrace_8374108 : CollatzResearch.WordTrace tailWord_8374108 prefixEnd_8374108 4299942456661027497638185 := by
  unfold tailWord_8374108
  simp only [CollatzResearch.WordTrace]
  refine ⟨152714405373022187314381489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203619207164029583085841985 152714405373022187314381489)
  ·
    refine ⟨114535804029766640485786117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152714405373022187314381489 114535804029766640485786117)
    ·
      refine ⟨21475463255581245091084897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114535804029766640485786117 21475463255581245091084897)
      ·
        refine ⟨16106597441685933818313673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21475463255581245091084897 16106597441685933818313673)
        ·
          refine ⟨12079948081264450363735255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16106597441685933818313673 12079948081264450363735255)
          ·
            refine ⟨18119922121896675545602883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079948081264450363735255 18119922121896675545602883)
            ·
              refine ⟨27179883182845013318404325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18119922121896675545602883 27179883182845013318404325)
              ·
                refine ⟨5096228096783439997200811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27179883182845013318404325 5096228096783439997200811)
                ·
                  refine ⟨7644342145175159995801217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096228096783439997200811 7644342145175159995801217)
                  ·
                    refine ⟨5733256608881369996850913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644342145175159995801217 5733256608881369996850913)
                    ·
                      refine ⟨4299942456661027497638185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733256608881369996850913 4299942456661027497638185)
                      ·
                        rfl

theorem cell23_8374108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_8374108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374108 prefixEnd_8374108 := by exact prefixLift 8374108
  have htrace : WordTrace (prefixWord ++ tailWord_8374108) baseStart_8374108 baseEnd_8374108 := by
    simpa [prefixWord, tailWord_8374108, baseEnd_8374108] using wordTrace_append hprefix tailTrace_8374108
  have hstable : (prefixWord ++ tailWord_8374108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374108).length < 2 ^ (prefixWord ++ tailWord_8374108).sum := by decide
  have hdescent : baseEnd_8374108 < baseStart_8374108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374113 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_8374113 : Nat := 118140960795 + 8374113 * 2 ^ 59
def prefixEnd_8374113 : Nat := 4983230072969 + 3 ^ 40 * 8374113 * 2
def baseEnd_8374113 : Nat := 4299945024064299978075661

theorem tailTrace_8374113 : CollatzResearch.WordTrace tailWord_8374113 prefixEnd_8374113 4299945024064299978075661 := by
  unfold tailWord_8374113
  simp only [CollatzResearch.WordTrace]
  refine ⟨305428993111026260482694993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203619328740684173655129995 305428993111026260482694993)
  ·
    refine ⟨229071744833269695362021245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305428993111026260482694993 229071744833269695362021245)
    ·
      refine ⟨85901904312476135760757967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229071744833269695362021245 85901904312476135760757967)
      ·
        refine ⟨128852856468714203641136951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85901904312476135760757967 128852856468714203641136951)
        ·
          refine ⟨193279284703071305461705427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128852856468714203641136951 193279284703071305461705427)
          ·
            refine ⟨289918927054606958192558141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193279284703071305461705427 289918927054606958192558141)
            ·
              refine ⟨108719597645477609322209303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289918927054606958192558141 108719597645477609322209303)
              ·
                refine ⟨163079396468216413983313955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108719597645477609322209303 163079396468216413983313955)
                ·
                  refine ⟨244619094702324620974970933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163079396468216413983313955 244619094702324620974970933)
                  ·
                    refine ⟨22933040128342933216403525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244619094702324620974970933 22933040128342933216403525)
                    ·
                      refine ⟨4299945024064299978075661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22933040128342933216403525 4299945024064299978075661)
                      ·
                        rfl

theorem cell23_8374113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_8374113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374113 prefixEnd_8374113 := by exact prefixLift 8374113
  have htrace : WordTrace (prefixWord ++ tailWord_8374113) baseStart_8374113 baseEnd_8374113 := by
    simpa [prefixWord, tailWord_8374113, baseEnd_8374113] using wordTrace_append hprefix tailTrace_8374113
  have hstable : (prefixWord ++ tailWord_8374113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374113).length < 2 ^ (prefixWord ++ tailWord_8374113).sum := by decide
  have hdescent : baseEnd_8374113 < baseStart_8374113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374143 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_8374143 : Nat := 118140960795 + 8374143 * 2 ^ 59
def prefixEnd_8374143 : Nat := 4983230072969 + 3 ^ 40 * 8374143 * 2
def baseEnd_8374143 : Nat := 4299960428483934860700523

theorem tailTrace_8374143 : CollatzResearch.WordTrace tailWord_8374143 prefixEnd_8374143 4299960428483934860700523 := by
  unfold tailWord_8374143
  simp only [CollatzResearch.WordTrace]
  refine ⟨305430087300917575606287083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203620058200611717070858055 305430087300917575606287083)
  ·
    refine ⟨458145130951376363409430625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305430087300917575606287083 458145130951376363409430625)
    ·
      refine ⟨343608848213532272557072969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458145130951376363409430625 343608848213532272557072969)
      ·
        refine ⟨257706636160149204417804727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343608848213532272557072969 257706636160149204417804727)
        ·
          refine ⟨386559954240223806626707091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257706636160149204417804727 386559954240223806626707091)
          ·
            refine ⟨579839931360335709940060637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386559954240223806626707091 579839931360335709940060637)
            ·
              refine ⟨217439974260125891227522739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579839931360335709940060637 217439974260125891227522739)
              ·
                refine ⟨326159961390188836841284109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217439974260125891227522739 326159961390188836841284109)
                ·
                  refine ⟨122309985521320813815481541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326159961390188836841284109 122309985521320813815481541)
                  ·
                    refine ⟨22933122285247652590402789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122309985521320813815481541 22933122285247652590402789)
                    ·
                      refine ⟨4299960428483934860700523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22933122285247652590402789 4299960428483934860700523)
                      ·
                        rfl

theorem cell23_8374143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_8374143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374143 prefixEnd_8374143 := by exact prefixLift 8374143
  have htrace : WordTrace (prefixWord ++ tailWord_8374143) baseStart_8374143 baseEnd_8374143 := by
    simpa [prefixWord, tailWord_8374143, baseEnd_8374143] using wordTrace_append hprefix tailTrace_8374143
  have hstable : (prefixWord ++ tailWord_8374143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374143).length < 2 ^ (prefixWord ++ tailWord_8374143).sum := by decide
  have hdescent : baseEnd_8374143 < baseStart_8374143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374147 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 1, 4, 2]
def baseStart_8374147 : Nat := 118140960795 + 8374147 * 2 ^ 59
def prefixEnd_8374147 : Nat := 4983230072969 + 3 ^ 40 * 8374147 * 2
def baseEnd_8374147 : Nat := 4299962482406552845050505

theorem tailTrace_8374147 : CollatzResearch.WordTrace tailWord_8374147 prefixEnd_8374147 4299962482406552845050505 := by
  unfold tailWord_8374147
  simp only [CollatzResearch.WordTrace]
  refine ⟨305430233192903084289432695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203620155461935389526288463 305430233192903084289432695)
  ·
    refine ⟨458145349789354626434149043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305430233192903084289432695 458145349789354626434149043)
    ·
      refine ⟨687218024684031939651223565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458145349789354626434149043 687218024684031939651223565)
      ·
        refine ⟨257706759256511977369208837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687218024684031939651223565 257706759256511977369208837)
        ·
          refine ⟨48320017360595995756726657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257706759256511977369208837 48320017360595995756726657)
          ·
            refine ⟨36240013020446996817544993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48320017360595995756726657 36240013020446996817544993)
            ·
              refine ⟨27180009765335247613158745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36240013020446996817544993 27180009765335247613158745)
              ·
                refine ⟨20385007324001435709869059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27180009765335247613158745 20385007324001435709869059)
                ·
                  refine ⟨30577510986002153564803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20385007324001435709869059 30577510986002153564803589)
                  ·
                    refine ⟨5733283309875403793400673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30577510986002153564803589 5733283309875403793400673)
                    ·
                      refine ⟨4299962482406552845050505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733283309875403793400673 4299962482406552845050505)
                      ·
                        rfl

theorem cell23_8374147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_8374147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374147 prefixEnd_8374147 := by exact prefixLift 8374147
  have htrace : WordTrace (prefixWord ++ tailWord_8374147) baseStart_8374147 baseEnd_8374147 := by
    simpa [prefixWord, tailWord_8374147, baseEnd_8374147] using wordTrace_append hprefix tailTrace_8374147
  have hstable : (prefixWord ++ tailWord_8374147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374147).length < 2 ^ (prefixWord ++ tailWord_8374147).sum := by decide
  have hdescent : baseEnd_8374147 < baseStart_8374147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374153 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 9]
def baseStart_8374153 : Nat := 118140960795 + 8374153 * 2 ^ 59
def prefixEnd_8374153 : Nat := 4983230072969 + 3 ^ 40 * 8374153 * 2
def baseEnd_8374153 : Nat := 477773951476719980175053

theorem tailTrace_8374153 : CollatzResearch.WordTrace tailWord_8374153 prefixEnd_8374153 477773951476719980175053 := by
  unfold tailWord_8374153
  simp only [CollatzResearch.WordTrace]
  refine ⟨305430452030881347314151113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203620301353920898209434075 305430452030881347314151113)
  ·
    refine ⟨229072839023161010485613335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305430452030881347314151113 229072839023161010485613335)
    ·
      refine ⟨343609258534741515728420003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229072839023161010485613335 343609258534741515728420003)
      ·
        refine ⟨515413887802112273592630005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343609258534741515728420003 515413887802112273592630005)
        ·
          refine ⟨48320051981448025649309063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515413887802112273592630005 48320051981448025649309063)
          ·
            refine ⟨72480077972172038473963595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48320051981448025649309063 72480077972172038473963595)
            ·
              refine ⟨108720116958258057710945393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72480077972172038473963595 108720116958258057710945393)
              ·
                refine ⟨81540087718693543283209045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108720116958258057710945393 81540087718693543283209045)
                ·
                  refine ⟨477773951476719980175053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81540087718693543283209045 477773951476719980175053)
                  ·
                    rfl

theorem cell23_8374153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_8374153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374153 prefixEnd_8374153 := by exact prefixLift 8374153
  have htrace : WordTrace (prefixWord ++ tailWord_8374153) baseStart_8374153 baseEnd_8374153 := by
    simpa [prefixWord, tailWord_8374153, baseEnd_8374153] using wordTrace_append hprefix tailTrace_8374153
  have hstable : (prefixWord ++ tailWord_8374153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374153).length < 2 ^ (prefixWord ++ tailWord_8374153).sum := by decide
  have hdescent : baseEnd_8374153 < baseStart_8374153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374158 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8374158 : Nat := 118140960795 + 8374158 * 2 ^ 59
def prefixEnd_8374158 : Nat := 4983230072969 + 3 ^ 40 * 8374158 * 2
def baseEnd_8374158 : Nat := 4299968130693752302012955

theorem tailTrace_8374158 : CollatzResearch.WordTrace tailWord_8374158 prefixEnd_8374158 4299968130693752302012955 := by
  unfold tailWord_8374158
  simp only [CollatzResearch.WordTrace]
  refine ⟨38178829299482904146010391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203620422930575488778722085 38178829299482904146010391)
  ·
    refine ⟨57268243949224356219015587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38178829299482904146010391 57268243949224356219015587)
    ·
      refine ⟨85902365923836534328523381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57268243949224356219015587 85902365923836534328523381)
      ·
        refine ⟨8053346805359675093299067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85902365923836534328523381 8053346805359675093299067)
        ·
          refine ⟨12080020208039512639948601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053346805359675093299067 12080020208039512639948601)
          ·
            refine ⟨9060015156029634479961451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12080020208039512639948601 9060015156029634479961451)
            ·
              refine ⟨13590022734044451719942177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060015156029634479961451 13590022734044451719942177)
              ·
                refine ⟨10192517050533338789956633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590022734044451719942177 10192517050533338789956633)
                ·
                  refine ⟨7644387787900004092467475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192517050533338789956633 7644387787900004092467475)
                  ·
                    refine ⟨11466581681850006138701213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7644387787900004092467475 11466581681850006138701213)
                    ·
                      refine ⟨4299968130693752302012955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466581681850006138701213 4299968130693752302012955)
                      ·
                        rfl

theorem cell23_8374158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8374158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374158 prefixEnd_8374158 := by exact prefixLift 8374158
  have htrace : WordTrace (prefixWord ++ tailWord_8374158) baseStart_8374158 baseEnd_8374158 := by
    simpa [prefixWord, tailWord_8374158, baseEnd_8374158] using wordTrace_append hprefix tailTrace_8374158
  have hstable : (prefixWord ++ tailWord_8374158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374158).length < 2 ^ (prefixWord ++ tailWord_8374158).sum := by decide
  have hdescent : baseEnd_8374158 < baseStart_8374158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374170 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_8374170 : Nat := 118140960795 + 8374170 * 2 ^ 59
def prefixEnd_8374170 : Nat := 4983230072969 + 3 ^ 40 * 8374170 * 2
def baseEnd_8374170 : Nat := 477774921384622917229211

theorem tailTrace_8374170 : CollatzResearch.WordTrace tailWord_8374170 prefixEnd_8374170 477774921384622917229211 := by
  unfold tailWord_8374170
  simp only [CollatzResearch.WordTrace]
  refine ⟨76357768017954939804379991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203620714714546506145013309 76357768017954939804379991)
  ·
    refine ⟨114536652026932409706569987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76357768017954939804379991 114536652026932409706569987)
    ·
      refine ⟨171804978040398614559854981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114536652026932409706569987 171804978040398614559854981)
      ·
        refine ⟨32213433382574740229972809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171804978040398614559854981 32213433382574740229972809)
        ·
          refine ⟨24160075036931055172479607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32213433382574740229972809 24160075036931055172479607)
          ·
            refine ⟨36240112555396582758719411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24160075036931055172479607 36240112555396582758719411)
            ·
              refine ⟨54360168833094874138079117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36240112555396582758719411 54360168833094874138079117)
              ·
                refine ⟨20385063312410577801779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54360168833094874138079117 20385063312410577801779669)
                ·
                  refine ⟨477774921384622917229211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20385063312410577801779669 477774921384622917229211)
                  ·
                    rfl

theorem cell23_8374170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_8374170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374170 prefixEnd_8374170 := by exact prefixLift 8374170
  have htrace : WordTrace (prefixWord ++ tailWord_8374170) baseStart_8374170 baseEnd_8374170 := by
    simpa [prefixWord, tailWord_8374170, baseEnd_8374170] using wordTrace_append hprefix tailTrace_8374170
  have hstable : (prefixWord ++ tailWord_8374170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374170).length < 2 ^ (prefixWord ++ tailWord_8374170).sum := by decide
  have hdescent : baseEnd_8374170 < baseStart_8374170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374200 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_8374200 : Nat := 118140960795 + 8374200 * 2 ^ 59
def prefixEnd_8374200 : Nat := 4983230072969 + 3 ^ 40 * 8374200 * 2
def baseEnd_8374200 : Nat := 1433329898960413712562587

theorem tailTrace_8374200 : CollatzResearch.WordTrace tailWord_8374200 prefixEnd_8374200 1433329898960413712562587 := by
  unfold tailWord_8374200
  simp only [CollatzResearch.WordTrace]
  refine ⟨152716083130855537170556027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203621444174474049560741369 152716083130855537170556027)
  ·
    refine ⟨229074124696283305755834041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152716083130855537170556027 229074124696283305755834041)
    ·
      refine ⟨171805593522212479316875531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229074124696283305755834041 171805593522212479316875531)
      ·
        refine ⟨257708390283318718975313297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171805593522212479316875531 257708390283318718975313297)
        ·
          refine ⟨193281292712489039231484973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257708390283318718975313297 193281292712489039231484973)
          ·
            refine ⟨72480484767183389711806865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193281292712489039231484973 72480484767183389711806865)
            ·
              refine ⟨54360363575387542283855149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72480484767183389711806865 54360363575387542283855149)
              ·
                refine ⟨20385136340770328356445681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54360363575387542283855149 20385136340770328356445681)
                ·
                  refine ⟨15288852255577746267334261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20385136340770328356445681 15288852255577746267334261)
                  ·
                    refine ⟨1433329898960413712562587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15288852255577746267334261 1433329898960413712562587)
                    ·
                      rfl

theorem cell23_8374200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_8374200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374200 prefixEnd_8374200 := by exact prefixLift 8374200
  have htrace : WordTrace (prefixWord ++ tailWord_8374200) baseStart_8374200 baseEnd_8374200 := by
    simpa [prefixWord, tailWord_8374200, baseEnd_8374200] using wordTrace_append hprefix tailTrace_8374200
  have hstable : (prefixWord ++ tailWord_8374200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374200).length < 2 ^ (prefixWord ++ tailWord_8374200).sum := by decide
  have hdescent : baseEnd_8374200 < baseStart_8374200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374240 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_8374240 : Nat := 118140960795 + 8374240 * 2 ^ 59
def prefixEnd_8374240 : Nat := 4983230072969 + 3 ^ 40 * 8374240 * 2
def baseEnd_8374240 : Nat := 4300010236107420981187577

theorem tailTrace_8374240 : CollatzResearch.WordTrace tailWord_8374240 prefixEnd_8374240 4300010236107420981187577 := by
  unfold tailWord_8374240
  simp only [CollatzResearch.WordTrace]
  refine ⟨152716812590783080586284087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203622416787710774115045449 152716812590783080586284087)
  ·
    refine ⟨229075218886174620879426131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152716812590783080586284087 229075218886174620879426131)
    ·
      refine ⟨343612828329261931319139197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229075218886174620879426131 343612828329261931319139197)
      ·
        refine ⟨128854810623473224244677199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343612828329261931319139197 128854810623473224244677199)
        ·
          refine ⟨193282215935209836367015799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128854810623473224244677199 193282215935209836367015799)
          ·
            refine ⟨289923323902814754550523699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193282215935209836367015799 289923323902814754550523699)
            ·
              refine ⟨434884985854222131825785549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289923323902814754550523699 434884985854222131825785549)
              ·
                refine ⟨163081869695333299434669581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434884985854222131825785549 163081869695333299434669581)
                ·
                  refine ⟨61155701135749987288001093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163081869695333299434669581 61155701135749987288001093)
                  ·
                    refine ⟨11466693962953122616500205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61155701135749987288001093 11466693962953122616500205)
                    ·
                      refine ⟨4300010236107420981187577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466693962953122616500205 4300010236107420981187577)
                      ·
                        rfl

theorem cell23_8374240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_8374240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374240 prefixEnd_8374240 := by exact prefixLift 8374240
  have htrace : WordTrace (prefixWord ++ tailWord_8374240) baseStart_8374240 baseEnd_8374240 := by
    simpa [prefixWord, tailWord_8374240, baseEnd_8374240] using wordTrace_append hprefix tailTrace_8374240
  have hstable : (prefixWord ++ tailWord_8374240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374240).length < 2 ^ (prefixWord ++ tailWord_8374240).sum := by decide
  have hdescent : baseEnd_8374240 < baseStart_8374240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374254 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_8374254 : Nat := 118140960795 + 8374254 * 2 ^ 59
def prefixEnd_8374254 : Nat := 4983230072969 + 3 ^ 40 * 8374254 * 2
def baseEnd_8374254 : Nat := 4300017424836583926412513

theorem tailTrace_8374254 : CollatzResearch.WordTrace tailWord_8374254 prefixEnd_8374254 4300017424836583926412513 := by
  unfold tailWord_8374254
  simp only [CollatzResearch.WordTrace]
  refine ⟨38179266975439430195447227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203622757202343627709051877 38179266975439430195447227)
  ·
    refine ⟨57268900463159145293170841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38179266975439430195447227 57268900463159145293170841)
    ·
      refine ⟨42951675347369358969878131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57268900463159145293170841 42951675347369358969878131)
      ·
        refine ⟨64427513021054038454817197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42951675347369358969878131 64427513021054038454817197)
        ·
          refine ⟨24160317382895264420556449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64427513021054038454817197 24160317382895264420556449)
          ·
            refine ⟨18120238037171448315417337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24160317382895264420556449 18120238037171448315417337)
            ·
              refine ⟨13590178527878586236563003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18120238037171448315417337 13590178527878586236563003)
              ·
                refine ⟨20385267791817879354844505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13590178527878586236563003 20385267791817879354844505)
                ·
                  refine ⟨15288950843863409516133379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20385267791817879354844505 15288950843863409516133379)
                  ·
                    refine ⟨22933426265795114274200069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15288950843863409516133379 22933426265795114274200069)
                    ·
                      refine ⟨4300017424836583926412513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22933426265795114274200069 4300017424836583926412513)
                      ·
                        rfl

theorem cell23_8374254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_8374254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374254 prefixEnd_8374254 := by exact prefixLift 8374254
  have htrace : WordTrace (prefixWord ++ tailWord_8374254) baseStart_8374254 baseEnd_8374254 := by
    simpa [prefixWord, tailWord_8374254, baseEnd_8374254] using wordTrace_append hprefix tailTrace_8374254
  have hstable : (prefixWord ++ tailWord_8374254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374254).length < 2 ^ (prefixWord ++ tailWord_8374254).sum := by decide
  have hdescent : baseEnd_8374254 < baseStart_8374254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374277 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 6]
def baseStart_8374277 : Nat := 118140960795 + 8374277 * 2 ^ 59
def prefixEnd_8374277 : Nat := 4983230072969 + 3 ^ 40 * 8374277 * 2
def baseEnd_8374277 : Nat := 477781026099070815158323

theorem tailTrace_8374277 : CollatzResearch.WordTrace tailWord_8374277 prefixEnd_8374277 477781026099070815158323 := by
  unfold tailWord_8374277
  simp only [CollatzResearch.WordTrace]
  refine ⟨305434974682432116491665085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203623316454954744327776723 305434974682432116491665085)
  ·
    refine ⟨114538115505912043684374407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305434974682432116491665085 114538115505912043684374407)
    ·
      refine ⟨171807173258868065526561611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114538115505912043684374407 171807173258868065526561611)
      ·
        refine ⟨257710759888302098289842417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171807173258868065526561611 257710759888302098289842417)
        ·
          refine ⟨193283069916226573717381813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257710759888302098289842417 193283069916226573717381813)
          ·
            refine ⟨18120287804646241286004545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193283069916226573717381813 18120287804646241286004545)
            ·
              refine ⟨13590215853484680964503409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18120287804646241286004545 13590215853484680964503409)
              ·
                refine ⟨10192661890113510723377557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590215853484680964503409 10192661890113510723377557)
                ·
                  refine ⟨477781026099070815158323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10192661890113510723377557 477781026099070815158323)
                  ·
                    rfl

theorem cell23_8374277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_8374277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374277 prefixEnd_8374277 := by exact prefixLift 8374277
  have htrace : WordTrace (prefixWord ++ tailWord_8374277) baseStart_8374277 baseEnd_8374277 := by
    simpa [prefixWord, tailWord_8374277, baseEnd_8374277] using wordTrace_append hprefix tailTrace_8374277
  have hstable : (prefixWord ++ tailWord_8374277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374277).length < 2 ^ (prefixWord ++ tailWord_8374277).sum := by decide
  have hdescent : baseEnd_8374277 < baseStart_8374277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374280 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_8374280 : Nat := 118140960795 + 8374280 * 2 ^ 59
def prefixEnd_8374280 : Nat := 4983230072969 + 3 ^ 40 * 8374280 * 2
def baseEnd_8374280 : Nat := 4300030775333600824687393

theorem tailTrace_8374280 : CollatzResearch.WordTrace tailWord_8374280 prefixEnd_8374280 4300030775333600824687393 := by
  unfold tailWord_8374280
  simp only [CollatzResearch.WordTrace]
  refine ⟨152717542050710624002012147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203623389400947498669349529 152717542050710624002012147)
  ·
    refine ⟨229076313076065936003018221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152717542050710624002012147 229076313076065936003018221)
    ·
      refine ⟨85903617403524726001131833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229076313076065936003018221 85903617403524726001131833)
      ·
        refine ⟨64427713052643544500848875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85903617403524726001131833 64427713052643544500848875)
        ·
          refine ⟨96641569578965316751273313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64427713052643544500848875 96641569578965316751273313)
          ·
            refine ⟨72481177184223987563454985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96641569578965316751273313 72481177184223987563454985)
            ·
              refine ⟨54360882888167990672591239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72481177184223987563454985 54360882888167990672591239)
              ·
                refine ⟨81541324332251986008886859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54360882888167990672591239 81541324332251986008886859)
                ·
                  refine ⟨122311986498377979013330289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81541324332251986008886859 122311986498377979013330289)
                  ·
                    refine ⟨91733989873783484259997717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122311986498377979013330289 91733989873783484259997717)
                    ·
                      refine ⟨4300030775333600824687393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91733989873783484259997717 4300030775333600824687393)
                      ·
                        rfl

theorem cell23_8374280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_8374280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374280 prefixEnd_8374280 := by exact prefixLift 8374280
  have htrace : WordTrace (prefixWord ++ tailWord_8374280) baseStart_8374280 baseEnd_8374280 := by
    simpa [prefixWord, tailWord_8374280, baseEnd_8374280] using wordTrace_append hprefix tailTrace_8374280
  have hstable : (prefixWord ++ tailWord_8374280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374280).length < 2 ^ (prefixWord ++ tailWord_8374280).sum := by decide
  have hdescent : baseEnd_8374280 < baseStart_8374280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374297 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 5, 2]
def baseStart_8374297 : Nat := 118140960795 + 8374297 * 2 ^ 59
def prefixEnd_8374297 : Nat := 4983230072969 + 3 ^ 40 * 8374297 * 2
def baseEnd_8374297 : Nat := 4300039504504727258174815

theorem tailTrace_8374297 : CollatzResearch.WordTrace tailWord_8374297 prefixEnd_8374297 4300039504504727258174815 := by
  unfold tailWord_8374297
  simp only [CollatzResearch.WordTrace]
  refine ⟨305435704142359659907393145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203623802761573106604928763 305435704142359659907393145)
  ·
    refine ⟨229076778106769744930544859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305435704142359659907393145 229076778106769744930544859)
    ·
      refine ⟨343615167160154617395817289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229076778106769744930544859 343615167160154617395817289)
      ·
        refine ⟨257711375370115963046862967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343615167160154617395817289 257711375370115963046862967)
        ·
          refine ⟨386567063055173944570294451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257711375370115963046862967 386567063055173944570294451)
          ·
            refine ⟨579850594582760916855441677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386567063055173944570294451 579850594582760916855441677)
            ·
              refine ⟨217443972968535343820790629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579850594582760916855441677 217443972968535343820790629)
              ·
                refine ⟨40770744931600376966398243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217443972968535343820790629 40770744931600376966398243)
                ·
                  refine ⟨61156117397400565449597365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40770744931600376966398243 61156117397400565449597365)
                  ·
                    refine ⟨5733386006006303010899753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61156117397400565449597365 5733386006006303010899753)
                    ·
                      refine ⟨4300039504504727258174815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733386006006303010899753 4300039504504727258174815)
                      ·
                        rfl

theorem cell23_8374297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_8374297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374297 prefixEnd_8374297 := by exact prefixLift 8374297
  have htrace : WordTrace (prefixWord ++ tailWord_8374297) baseStart_8374297 baseEnd_8374297 := by
    simpa [prefixWord, tailWord_8374297, baseEnd_8374297] using wordTrace_append hprefix tailTrace_8374297
  have hstable : (prefixWord ++ tailWord_8374297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374297).length < 2 ^ (prefixWord ++ tailWord_8374297).sum := by decide
  have hdescent : baseEnd_8374297 < baseStart_8374297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374307 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 1, 5]
def baseStart_8374307 : Nat := 118140960795 + 8374307 * 2 ^ 59
def prefixEnd_8374307 : Nat := 4983230072969 + 3 ^ 40 * 8374307 * 2
def baseEnd_8374307 : Nat := 1433348213103757406349923

theorem tailTrace_8374307 : CollatzResearch.WordTrace tailWord_8374307 prefixEnd_8374307 1433348213103757406349923 := by
  unfold tailWord_8374307
  simp only [CollatzResearch.WordTrace]
  refine ⟨305436068872323431615257175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203624045914882287743504783 305436068872323431615257175)
  ·
    refine ⟨458154103308485147422885763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305436068872323431615257175 458154103308485147422885763)
    ·
      refine ⟨687231154962727721134328645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458154103308485147422885763 687231154962727721134328645)
      ·
        refine ⟨128855841555511447712686621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 687231154962727721134328645 128855841555511447712686621)
        ·
          refine ⟨48320940583316792892257483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128855841555511447712686621 48320940583316792892257483)
          ·
            refine ⟨72481410874975189338386225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48320940583316792892257483 72481410874975189338386225)
            ·
              refine ⟨54361058156231392003789669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72481410874975189338386225 54361058156231392003789669)
              ·
                refine ⟨10192698404293386000710563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54361058156231392003789669 10192698404293386000710563)
                ·
                  refine ⟨15289047606440079001065845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192698404293386000710563 15289047606440079001065845)
                  ·
                    refine ⟨1433348213103757406349923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15289047606440079001065845 1433348213103757406349923)
                    ·
                      rfl

theorem cell23_8374307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 5].length) (baseStart_8374307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374307 prefixEnd_8374307 := by exact prefixLift 8374307
  have htrace : WordTrace (prefixWord ++ tailWord_8374307) baseStart_8374307 baseEnd_8374307 := by
    simpa [prefixWord, tailWord_8374307, baseEnd_8374307] using wordTrace_append hprefix tailTrace_8374307
  have hstable : (prefixWord ++ tailWord_8374307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374307).length < 2 ^ (prefixWord ++ tailWord_8374307).sum := by decide
  have hdescent : baseEnd_8374307 < baseStart_8374307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374308 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_8374308 : Nat := 118140960795 + 8374308 * 2 ^ 59
def prefixEnd_8374308 : Nat := 4983230072969 + 3 ^ 40 * 8374308 * 2
def baseEnd_8374308 : Nat := 4300045152791926715137265

theorem tailTrace_8374308 : CollatzResearch.WordTrace tailWord_8374308 prefixEnd_8374308 4300045152791926715137265 := by
  unfold tailWord_8374308
  simp only [CollatzResearch.WordTrace]
  refine ⟨152718052672659904393021789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203624070230213205857362385 152718052672659904393021789)
  ·
    refine ⟨57269269752247464147383171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152718052672659904393021789 57269269752247464147383171)
    ·
      refine ⟨85903904628371196221074757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57269269752247464147383171 85903904628371196221074757)
      ·
        refine ⟨16106982117819599291451517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85903904628371196221074757 16106982117819599291451517)
        ·
          refine ⟨6040118294182349734294319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16106982117819599291451517 6040118294182349734294319)
          ·
            refine ⟨9060177441273524601441479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040118294182349734294319 9060177441273524601441479)
            ·
              refine ⟨13590266161910286902162219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060177441273524601441479 13590266161910286902162219)
              ·
                refine ⟨20385399242865430353243329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13590266161910286902162219 20385399242865430353243329)
                ·
                  refine ⟨15289049432149072764932497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20385399242865430353243329 15289049432149072764932497)
                  ·
                    refine ⟨11466787074111804573699373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15289049432149072764932497 11466787074111804573699373)
                    ·
                      refine ⟨4300045152791926715137265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466787074111804573699373 4300045152791926715137265)
                      ·
                        rfl

theorem cell23_8374308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_8374308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374308 prefixEnd_8374308 := by exact prefixLift 8374308
  have htrace : WordTrace (prefixWord ++ tailWord_8374308) baseStart_8374308 baseEnd_8374308 := by
    simpa [prefixWord, tailWord_8374308, baseEnd_8374308] using wordTrace_append hprefix tailTrace_8374308
  have hstable : (prefixWord ++ tailWord_8374308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374308).length < 2 ^ (prefixWord ++ tailWord_8374308).sum := by decide
  have hdescent : baseEnd_8374308 < baseStart_8374308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374321 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 1, 1, 3]
def baseStart_8374321 : Nat := 118140960795 + 8374321 * 2 ^ 59
def prefixEnd_8374321 : Nat := 4983230072969 + 3 ^ 40 * 8374321 * 2
def baseEnd_8374321 : Nat := 4300051828040435164274705

theorem tailTrace_8374321 : CollatzResearch.WordTrace tailWord_8374321 prefixEnd_8374321 4300051828040435164274705 := by
  unfold tailWord_8374321
  simp only [CollatzResearch.WordTrace]
  refine ⟨305436579494272712006266817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203624386329515141337511211 305436579494272712006266817)
  ·
    refine ⟨229077434620704534004700113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305436579494272712006266817 229077434620704534004700113)
    ·
      refine ⟨171808075965528400503525085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229077434620704534004700113 171808075965528400503525085)
      ·
        refine ⟨64428028487073150188821907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171808075965528400503525085 64428028487073150188821907)
        ·
          refine ⟨96642042730609725283232861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64428028487073150188821907 96642042730609725283232861)
          ·
            refine ⟨36240766023978646981212323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96642042730609725283232861 36240766023978646981212323)
            ·
              refine ⟨54361149035967970471818485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36240766023978646981212323 54361149035967970471818485)
              ·
                refine ⟨5096357722121997231732983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54361149035967970471818485 5096357722121997231732983)
                ·
                  refine ⟨7644536583182995847599475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096357722121997231732983 7644536583182995847599475)
                  ·
                    refine ⟨11466804874774493771399213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7644536583182995847599475 11466804874774493771399213)
                    ·
                      refine ⟨4300051828040435164274705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466804874774493771399213 4300051828040435164274705)
                      ·
                        rfl

theorem cell23_8374321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_8374321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374321 prefixEnd_8374321 := by exact prefixLift 8374321
  have htrace : WordTrace (prefixWord ++ tailWord_8374321) baseStart_8374321 baseEnd_8374321 := by
    simpa [prefixWord, tailWord_8374321, baseEnd_8374321] using wordTrace_append hprefix tailTrace_8374321
  have hstable : (prefixWord ++ tailWord_8374321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374321).length < 2 ^ (prefixWord ++ tailWord_8374321).sum := by decide
  have hdescent : baseEnd_8374321 < baseStart_8374321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374357 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_8374357 : Nat := 118140960795 + 8374357 * 2 ^ 59
def prefixEnd_8374357 : Nat := 4983230072969 + 3 ^ 40 * 8374357 * 2
def baseEnd_8374357 : Nat := 4300070313343997023424539

theorem tailTrace_8374357 : CollatzResearch.WordTrace tailWord_8374357 prefixEnd_8374357 4300070313343997023424539 := by
  unfold tailWord_8374357
  simp only [CollatzResearch.WordTrace]
  refine ⟨305437892522142290154577325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203625261681428193436384883 305437892522142290154577325)
  ·
    refine ⟨114539209695803358807966497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305437892522142290154577325 114539209695803358807966497)
    ·
      refine ⟨85904407271852519105974873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114539209695803358807966497 85904407271852519105974873)
      ·
        refine ⟨64428305453889389329481155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85904407271852519105974873 64428305453889389329481155)
        ·
          refine ⟨96642458180834083994221733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64428305453889389329481155 96642458180834083994221733)
          ·
            refine ⟨18120460908906390748916575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96642458180834083994221733 18120460908906390748916575)
            ·
              refine ⟨27180691363359586123374863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18120460908906390748916575 27180691363359586123374863)
              ·
                refine ⟨40771037045039379185062295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27180691363359586123374863 40771037045039379185062295)
                ·
                  refine ⟨61156555567559068777593443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40771037045039379185062295 61156555567559068777593443)
                  ·
                    refine ⟨91734833351338603166390165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61156555567559068777593443 91734833351338603166390165)
                    ·
                      refine ⟨4300070313343997023424539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91734833351338603166390165 4300070313343997023424539)
                      ·
                        rfl

theorem cell23_8374357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_8374357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374357 prefixEnd_8374357 := by exact prefixLift 8374357
  have htrace : WordTrace (prefixWord ++ tailWord_8374357) baseStart_8374357 baseEnd_8374357 := by
    simpa [prefixWord, tailWord_8374357, baseEnd_8374357] using wordTrace_append hprefix tailTrace_8374357
  have hstable : (prefixWord ++ tailWord_8374357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374357).length < 2 ^ (prefixWord ++ tailWord_8374357).sum := by decide
  have hdescent : baseEnd_8374357 < baseStart_8374357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374358 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_8374358 : Nat := 118140960795 + 8374358 * 2 ^ 59
def prefixEnd_8374358 : Nat := 4983230072969 + 3 ^ 40 * 8374358 * 2
def baseEnd_8374358 : Nat := 1433356942274883839837345

theorem tailTrace_8374358 : CollatzResearch.WordTrace tailWord_8374358 prefixEnd_8374358 1433356942274883839837345 := by
  unfold tailWord_8374358
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089870562196166707835233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203625285996759111550242485 19089870562196166707835233)
  ·
    refine ⟨14317402921647125030876425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19089870562196166707835233 14317402921647125030876425)
    ·
      refine ⟨10738052191235343773157319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14317402921647125030876425 10738052191235343773157319)
      ·
        refine ⟨16107078286853015659735979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738052191235343773157319 16107078286853015659735979)
        ·
          refine ⟨24160617430279523489603969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16107078286853015659735979 24160617430279523489603969)
          ·
            refine ⟨18120463072709642617202977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24160617430279523489603969 18120463072709642617202977)
            ·
              refine ⟨13590347304532231962902233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18120463072709642617202977 13590347304532231962902233)
              ·
                refine ⟨10192760478399173972176675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590347304532231962902233 10192760478399173972176675)
                ·
                  refine ⟨15289140717598760958265013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10192760478399173972176675 15289140717598760958265013)
                  ·
                    refine ⟨1433356942274883839837345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15289140717598760958265013 1433356942274883839837345)
                    ·
                      rfl

theorem cell23_8374358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_8374358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374358 prefixEnd_8374358 := by exact prefixLift 8374358
  have htrace : WordTrace (prefixWord ++ tailWord_8374358) baseStart_8374358 baseEnd_8374358 := by
    simpa [prefixWord, tailWord_8374358, baseEnd_8374358] using wordTrace_append hprefix tailTrace_8374358
  have hstable : (prefixWord ++ tailWord_8374358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374358).length < 2 ^ (prefixWord ++ tailWord_8374358).sum := by decide
  have hdescent : baseEnd_8374358 < baseStart_8374358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374377 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_8374377 : Nat := 118140960795 + 8374377 * 2 ^ 59
def prefixEnd_8374377 : Nat := 4983230072969 + 3 ^ 40 * 8374377 * 2
def baseEnd_8374377 : Nat := 4300080582957086945174447

theorem tailTrace_8374377 : CollatzResearch.WordTrace tailWord_8374377 prefixEnd_8374377 4300080582957086945174447 := by
  unfold tailWord_8374377
  simp only [CollatzResearch.WordTrace]
  refine ⟨305438621982069833570305385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203625747988046555713536923 305438621982069833570305385)
  ·
    refine ⟨229078966486552375177729039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305438621982069833570305385 229078966486552375177729039)
    ·
      refine ⟨343618449729828562766593559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229078966486552375177729039 343618449729828562766593559)
      ·
        refine ⟨515427674594742844149890339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343618449729828562766593559 515427674594742844149890339)
        ·
          refine ⟨773141511892114266224835509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515427674594742844149890339 773141511892114266224835509)
          ·
            refine ⟨72482016739885712458578329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 773141511892114266224835509 72482016739885712458578329)
            ·
              refine ⟨54361512554914284343933747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72482016739885712458578329 54361512554914284343933747)
              ·
                refine ⟨81542268832371426515900621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54361512554914284343933747 81542268832371426515900621)
                ·
                  refine ⟨30578350812139284943462733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81542268832371426515900621 30578350812139284943462733)
                  ·
                    refine ⟨11466881554552231853798525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30578350812139284943462733 11466881554552231853798525)
                    ·
                      refine ⟨4300080582957086945174447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11466881554552231853798525 4300080582957086945174447)
                      ·
                        rfl

theorem cell23_8374377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_8374377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374377 prefixEnd_8374377 := by exact prefixLift 8374377
  have htrace : WordTrace (prefixWord ++ tailWord_8374377) baseStart_8374377 baseEnd_8374377 := by
    simpa [prefixWord, tailWord_8374377, baseEnd_8374377] using wordTrace_append hprefix tailTrace_8374377
  have hstable : (prefixWord ++ tailWord_8374377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374377).length < 2 ^ (prefixWord ++ tailWord_8374377).sum := by decide
  have hdescent : baseEnd_8374377 < baseStart_8374377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374437 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_8374437 : Nat := 118140960795 + 8374437 * 2 ^ 59
def prefixEnd_8374437 : Nat := 4983230072969 + 3 ^ 40 * 8374437 * 2
def baseEnd_8374437 : Nat := 4300111391796356710424171

theorem tailTrace_8374437 : CollatzResearch.WordTrace tailWord_8374437 prefixEnd_8374437 4300111391796356710424171 := by
  unfold tailWord_8374437
  simp only [CollatzResearch.WordTrace]
  refine ⟨305440810361852463817489565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203627206907901642544993043 305440810361852463817489565)
  ·
    refine ⟨114540303885694673931558587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305440810361852463817489565 114540303885694673931558587)
    ·
      refine ⟨171810455828542010897337881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114540303885694673931558587 171810455828542010897337881)
      ·
        refine ⟨128857841871406508173003411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171810455828542010897337881 128857841871406508173003411)
        ·
          refine ⟨193286762807109762259505117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128857841871406508173003411 193286762807109762259505117)
          ·
            refine ⟨72482536052666160847314419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193286762807109762259505117 72482536052666160847314419)
            ·
              refine ⟨108723804078999241270971629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72482536052666160847314419 108723804078999241270971629)
              ·
                refine ⟨40771426529624715476614361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108723804078999241270971629 40771426529624715476614361)
                ·
                  refine ⟨30578569897218536607460771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40771426529624715476614361 30578569897218536607460771)
                  ·
                    refine ⟨45867854845827804911191157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30578569897218536607460771 45867854845827804911191157)
                    ·
                      refine ⟨4300111391796356710424171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45867854845827804911191157 4300111391796356710424171)
                      ·
                        rfl

theorem cell23_8374437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_8374437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374437 prefixEnd_8374437 := by exact prefixLift 8374437
  have htrace : WordTrace (prefixWord ++ tailWord_8374437) baseStart_8374437 baseEnd_8374437 := by
    simpa [prefixWord, tailWord_8374437, baseEnd_8374437] using wordTrace_append hprefix tailTrace_8374437
  have hstable : (prefixWord ++ tailWord_8374437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374437).length < 2 ^ (prefixWord ++ tailWord_8374437).sum := by decide
  have hdescent : baseEnd_8374437 < baseStart_8374437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374446 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8374446 : Nat := 118140960795 + 8374446 * 2 ^ 59
def prefixEnd_8374446 : Nat := 4983230072969 + 3 ^ 40 * 8374446 * 2
def baseEnd_8374446 : Nat := 4300116013122247175211631

theorem tailTrace_8374446 : CollatzResearch.WordTrace tailWord_8374446 prefixEnd_8374446 4300116013122247175211631 := by
  unfold tailWord_8374446
  simp only [CollatzResearch.WordTrace]
  refine ⟨38180142327352482294320899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203627425745879905569711461 38180142327352482294320899)
  ·
    refine ⟨57270213491028723441481349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38180142327352482294320899 57270213491028723441481349)
    ·
      refine ⟨10738165029567885645277753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57270213491028723441481349 10738165029567885645277753)
      ·
        refine ⟨8053623772175914233958315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10738165029567885645277753 8053623772175914233958315)
        ·
          refine ⟨12080435658263871350937473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053623772175914233958315 12080435658263871350937473)
          ·
            refine ⟨9060326743697903513203105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12080435658263871350937473 9060326743697903513203105)
            ·
              refine ⟨6795245057773427634902329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9060326743697903513203105 6795245057773427634902329)
              ·
                refine ⟨5096433793330070726176747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795245057773427634902329 5096433793330070726176747)
                ·
                  refine ⟨7644650689995106089265121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096433793330070726176747 7644650689995106089265121)
                  ·
                    refine ⟨5733488017496329566948841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644650689995106089265121 5733488017496329566948841)
                    ·
                      refine ⟨4300116013122247175211631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733488017496329566948841 4300116013122247175211631)
                      ·
                        rfl

theorem cell23_8374446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8374446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374446 prefixEnd_8374446 := by exact prefixLift 8374446
  have htrace : WordTrace (prefixWord ++ tailWord_8374446) baseStart_8374446 baseEnd_8374446 := by
    simpa [prefixWord, tailWord_8374446, baseEnd_8374446] using wordTrace_append hprefix tailTrace_8374446
  have hstable : (prefixWord ++ tailWord_8374446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374446).length < 2 ^ (prefixWord ++ tailWord_8374446).sum := by decide
  have hdescent : baseEnd_8374446 < baseStart_8374446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374447 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_8374447 : Nat := 118140960795 + 8374447 * 2 ^ 59
def prefixEnd_8374447 : Nat := 4983230072969 + 3 ^ 40 * 8374447 * 2
def baseEnd_8374447 : Nat := 4300116526602901671299125

theorem tailTrace_8374447 : CollatzResearch.WordTrace tailWord_8374447 prefixEnd_8374447 4300116526602901671299125 := by
  unfold tailWord_8374447
  simp only [CollatzResearch.WordTrace]
  refine ⟨305441175091816235525353595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203627450061210823683569063 305441175091816235525353595)
  ·
    refine ⟨458161762637724353288030393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305441175091816235525353595 458161762637724353288030393)
    ·
      refine ⟨343621321978293264966022795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458161762637724353288030393 343621321978293264966022795)
      ·
        refine ⟨515431982967439897449034193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343621321978293264966022795 515431982967439897449034193)
        ·
          refine ⟨386573987225579923086775645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515431982967439897449034193 386573987225579923086775645)
          ·
            refine ⟨144965245209592471157540867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386573987225579923086775645 144965245209592471157540867)
            ·
              refine ⟨217447867814388706736311301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144965245209592471157540867 217447867814388706736311301)
              ·
                refine ⟨40771475215197882513058369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217447867814388706736311301 40771475215197882513058369)
                ·
                  refine ⟨30578606411398411884793777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40771475215197882513058369 30578606411398411884793777)
                  ·
                    refine ⟨22933954808548808913595333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30578606411398411884793777 22933954808548808913595333)
                    ·
                      refine ⟨4300116526602901671299125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22933954808548808913595333 4300116526602901671299125)
                      ·
                        rfl

theorem cell23_8374447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_8374447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374447 prefixEnd_8374447 := by exact prefixLift 8374447
  have htrace : WordTrace (prefixWord ++ tailWord_8374447) baseStart_8374447 baseEnd_8374447 := by
    simpa [prefixWord, tailWord_8374447, baseEnd_8374447] using wordTrace_append hprefix tailTrace_8374447
  have hstable : (prefixWord ++ tailWord_8374447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374447).length < 2 ^ (prefixWord ++ tailWord_8374447).sum := by decide
  have hdescent : baseEnd_8374447 < baseStart_8374447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374457 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 7]
def baseStart_8374457 : Nat := 118140960795 + 8374457 * 2 ^ 59
def prefixEnd_8374457 : Nat := 4983230072969 + 3 ^ 40 * 8374457 * 2
def baseEnd_8374457 : Nat := 477791295712160736908231

theorem tailTrace_8374457 : CollatzResearch.WordTrace tailWord_8374457 prefixEnd_8374457 477791295712160736908231 := by
  unfold tailWord_8374457
  simp only [CollatzResearch.WordTrace]
  refine ⟨305441539821780007233217625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203627693214520004822145083 305441539821780007233217625)
  ·
    refine ⟨229081154866335005424913219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305441539821780007233217625 229081154866335005424913219)
    ·
      refine ⟨343621732299502508137369829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229081154866335005424913219 343621732299502508137369829)
      ·
        refine ⟨64429074806156720275756843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343621732299502508137369829 64429074806156720275756843)
        ·
          refine ⟨96643612209235080413635265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64429074806156720275756843 96643612209235080413635265)
          ·
            refine ⟨72482709156926310310226449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96643612209235080413635265 72482709156926310310226449)
            ·
              refine ⟨54362031867694732732669837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72482709156926310310226449 54362031867694732732669837)
              ·
                refine ⟨20385761950385524774751189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54362031867694732732669837 20385761950385524774751189)
                ·
                  refine ⟨477791295712160736908231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20385761950385524774751189 477791295712160736908231)
                  ·
                    rfl

theorem cell23_8374457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_8374457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374457 prefixEnd_8374457 := by exact prefixLift 8374457
  have htrace : WordTrace (prefixWord ++ tailWord_8374457) baseStart_8374457 baseEnd_8374457 := by
    simpa [prefixWord, tailWord_8374457, baseEnd_8374457] using wordTrace_append hprefix tailTrace_8374457
  have hstable : (prefixWord ++ tailWord_8374457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374457).length < 2 ^ (prefixWord ++ tailWord_8374457).sum := by decide
  have hdescent : baseEnd_8374457 < baseStart_8374457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374464 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_8374464 : Nat := 118140960795 + 8374464 * 2 ^ 59
def prefixEnd_8374464 : Nat := 4983230072969 + 3 ^ 40 * 8374464 * 2
def baseEnd_8374464 : Nat := 4300125255774028104786547

theorem tailTrace_8374464 : CollatzResearch.WordTrace tailWord_8374464 prefixEnd_8374464 4300125255774028104786547 := by
  unfold tailWord_8374464
  simp only [CollatzResearch.WordTrace]
  refine ⟨152720897566377323714361223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203627863421836431619148297 152720897566377323714361223)
  ·
    refine ⟨229081346349565985571541835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152720897566377323714361223 229081346349565985571541835)
    ·
      refine ⟨343622019524348978357312753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229081346349565985571541835 343622019524348978357312753)
      ·
        refine ⟨257716514643261733767984565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343622019524348978357312753 257716514643261733767984565)
        ·
          refine ⟨24160923247805787540748553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257716514643261733767984565 24160923247805787540748553)
          ·
            refine ⟨18120692435854340655561415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24160923247805787540748553 18120692435854340655561415)
            ·
              refine ⟨27181038653781510983342123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18120692435854340655561415 27181038653781510983342123)
              ·
                refine ⟨40771557980672266475013185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27181038653781510983342123 40771557980672266475013185)
                ·
                  refine ⟨30578668485504199856259889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40771557980672266475013185 30578668485504199856259889)
                  ·
                    refine ⟨22934001364128149892194917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30578668485504199856259889 22934001364128149892194917)
                    ·
                      refine ⟨4300125255774028104786547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22934001364128149892194917 4300125255774028104786547)
                      ·
                        rfl

theorem cell23_8374464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_8374464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374464 prefixEnd_8374464 := by exact prefixLift 8374464
  have htrace : WordTrace (prefixWord ++ tailWord_8374464) baseStart_8374464 baseEnd_8374464 := by
    simpa [prefixWord, tailWord_8374464, baseEnd_8374464] using wordTrace_append hprefix tailTrace_8374464
  have hstable : (prefixWord ++ tailWord_8374464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374464).length < 2 ^ (prefixWord ++ tailWord_8374464).sum := by decide
  have hdescent : baseEnd_8374464 < baseStart_8374464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374468 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_8374468 : Nat := 118140960795 + 8374468 * 2 ^ 59
def prefixEnd_8374468 : Nat := 4983230072969 + 3 ^ 40 * 8374468 * 2
def baseEnd_8374468 : Nat := 4300127309696646089136529

theorem tailTrace_8374468 : CollatzResearch.WordTrace tailWord_8374468 prefixEnd_8374468 4300127309696646089136529 := by
  unfold tailWord_8374468
  simp only [CollatzResearch.WordTrace]
  refine ⟨152720970512370078055934029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203627960683160104074578705 152720970512370078055934029)
  ·
    refine ⟨57270363942138779270975261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152720970512370078055934029 57270363942138779270975261)
    ·
      refine ⟨21476386478302042226615723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57270363942138779270975261 21476386478302042226615723)
      ·
        refine ⟨32214579717453063339923585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21476386478302042226615723 32214579717453063339923585)
        ·
          refine ⟨24160934788089797504942689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32214579717453063339923585 24160934788089797504942689)
          ·
            refine ⟨18120701091067348128707017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24160934788089797504942689 18120701091067348128707017)
            ·
              refine ⟨13590525818300511096530263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18120701091067348128707017 13590525818300511096530263)
              ·
                refine ⟨20385788727450766644795395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13590525818300511096530263 20385788727450766644795395)
                ·
                  refine ⟨30578683091176149967193093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20385788727450766644795395 30578683091176149967193093)
                  ·
                    refine ⟨5733503079595528118848705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30578683091176149967193093 5733503079595528118848705)
                    ·
                      refine ⟨4300127309696646089136529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733503079595528118848705 4300127309696646089136529)
                      ·
                        rfl

theorem cell23_8374468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_8374468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374468 prefixEnd_8374468 := by exact prefixLift 8374468
  have htrace : WordTrace (prefixWord ++ tailWord_8374468) baseStart_8374468 baseEnd_8374468 := by
    simpa [prefixWord, tailWord_8374468, baseEnd_8374468] using wordTrace_append hprefix tailTrace_8374468
  have hstable : (prefixWord ++ tailWord_8374468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374468).length < 2 ^ (prefixWord ++ tailWord_8374468).sum := by decide
  have hdescent : baseEnd_8374468 < baseStart_8374468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374524 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_8374524 : Nat := 118140960795 + 8374524 * 2 ^ 59
def prefixEnd_8374524 : Nat := 4983230072969 + 3 ^ 40 * 8374524 * 2
def baseEnd_8374524 : Nat := 4300156064613297870036271

theorem tailTrace_8374524 : CollatzResearch.WordTrace tailWord_8374524 prefixEnd_8374524 4300156064613297870036271 := by
  unfold tailWord_8374524
  simp only [CollatzResearch.WordTrace]
  refine ⟨152721991756268638837953313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203629322341691518450604417 152721991756268638837953313)
  ·
    refine ⟨114541493817201479128464985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152721991756268638837953313 114541493817201479128464985)
    ·
      refine ⟨85906120362901109346348739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114541493817201479128464985 85906120362901109346348739)
      ·
        refine ⟨128859180544351664019523109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85906120362901109346348739 128859180544351664019523109)
        ·
          refine ⟨24161096352065937003660583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128859180544351664019523109 24161096352065937003660583)
          ·
            refine ⟨36241644528098905505490875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161096352065937003660583 36241644528098905505490875)
            ·
              refine ⟨54362466792148358258236313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241644528098905505490875 54362466792148358258236313)
              ·
                refine ⟨40771850094111268693677235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54362466792148358258236313 40771850094111268693677235)
                ·
                  refine ⟨61157775141166903040515853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40771850094111268693677235 61157775141166903040515853)
                  ·
                    refine ⟨22934165677937588640193445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61157775141166903040515853 22934165677937588640193445)
                    ·
                      refine ⟨4300156064613297870036271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22934165677937588640193445 4300156064613297870036271)
                      ·
                        rfl

theorem cell23_8374524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_8374524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374524 prefixEnd_8374524 := by exact prefixLift 8374524
  have htrace : WordTrace (prefixWord ++ tailWord_8374524) baseStart_8374524 baseEnd_8374524 := by
    simpa [prefixWord, tailWord_8374524, baseEnd_8374524] using wordTrace_append hprefix tailTrace_8374524
  have hstable : (prefixWord ++ tailWord_8374524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374524).length < 2 ^ (prefixWord ++ tailWord_8374524).sum := by decide
  have hdescent : baseEnd_8374524 < baseStart_8374524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374558 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_8374558 : Nat := 118140960795 + 8374558 * 2 ^ 59
def prefixEnd_8374558 : Nat := 4983230072969 + 3 ^ 40 * 8374558 * 2
def baseEnd_8374558 : Nat := 4300173522955550737011115

theorem tailTrace_8374558 : CollatzResearch.WordTrace tailWord_8374558 prefixEnd_8374558 4300173522955550737011115 := by
  unfold tailWord_8374558
  simp only [CollatzResearch.WordTrace]
  refine ⟨38180652949301762685330541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203630149062942734321762885 38180652949301762685330541)
  ·
    refine ⟨14317744855988161006998953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38180652949301762685330541 14317744855988161006998953)
    ·
      refine ⟨10738308641991120755249215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14317744855988161006998953 10738308641991120755249215)
      ·
        refine ⟨16107462962986681132873823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738308641991120755249215 16107462962986681132873823)
        ·
          refine ⟨24161194444480021699310735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16107462962986681132873823 24161194444480021699310735)
          ·
            refine ⟨36241791666720032548966103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161194444480021699310735 36241791666720032548966103)
            ·
              refine ⟨54362687500080048823449155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241791666720032548966103 54362687500080048823449155)
              ·
                refine ⟨81544031250120073235173733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54362687500080048823449155 81544031250120073235173733)
                ·
                  refine ⟨15289505859397513731595075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81544031250120073235173733 15289505859397513731595075)
                  ·
                    refine ⟨22934258789096270597392613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15289505859397513731595075 22934258789096270597392613)
                    ·
                      refine ⟨4300173522955550737011115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22934258789096270597392613 4300173522955550737011115)
                      ·
                        rfl

theorem cell23_8374558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_8374558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374558 prefixEnd_8374558 := by exact prefixLift 8374558
  have htrace : WordTrace (prefixWord ++ tailWord_8374558) baseStart_8374558 baseEnd_8374558 := by
    simpa [prefixWord, tailWord_8374558, baseEnd_8374558] using wordTrace_append hprefix tailTrace_8374558
  have hstable : (prefixWord ++ tailWord_8374558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374558).length < 2 ^ (prefixWord ++ tailWord_8374558).sum := by decide
  have hdescent : baseEnd_8374558 < baseStart_8374558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374564 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 8]
def baseStart_8374564 : Nat := 118140960795 + 8374564 * 2 ^ 59
def prefixEnd_8374564 : Nat := 4983230072969 + 3 ^ 40 * 8374564 * 2
def baseEnd_8374564 : Nat := 477797400426608634837343

theorem tailTrace_8374564 : CollatzResearch.WordTrace tailWord_8374564 prefixEnd_8374564 477797400426608634837343 := by
  unfold tailWord_8374564
  simp only [CollatzResearch.WordTrace]
  refine ⟨152722721216196182253681373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203630294954928243004908497 152722721216196182253681373)
  ·
    refine ⟨57271020456073568345130515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152722721216196182253681373 57271020456073568345130515)
    ·
      refine ⟨85906530684110352517695773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57271020456073568345130515 85906530684110352517695773)
      ·
        refine ⟨32214949006541382194135915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85906530684110352517695773 32214949006541382194135915)
        ·
          refine ⟨48322423509812073291203873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32214949006541382194135915 48322423509812073291203873)
          ·
            refine ⟨36241817632359054968402905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48322423509812073291203873 36241817632359054968402905)
            ·
              refine ⟨27181363224269291226302179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36241817632359054968402905 27181363224269291226302179)
              ·
                refine ⟨40772044836403936839453269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27181363224269291226302179 40772044836403936839453269)
                ·
                  refine ⟨477797400426608634837343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40772044836403936839453269 477797400426608634837343)
                  ·
                    rfl

theorem cell23_8374564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_8374564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374564 prefixEnd_8374564 := by exact prefixLift 8374564
  have htrace : WordTrace (prefixWord ++ tailWord_8374564) baseStart_8374564 baseEnd_8374564 := by
    simpa [prefixWord, tailWord_8374564, baseEnd_8374564] using wordTrace_append hprefix tailTrace_8374564
  have hstable : (prefixWord ++ tailWord_8374564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374564).length < 2 ^ (prefixWord ++ tailWord_8374564).sum := by decide
  have hdescent : baseEnd_8374564 < baseStart_8374564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374591 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 3]
def baseStart_8374591 : Nat := 118140960795 + 8374591 * 2 ^ 59
def prefixEnd_8374591 : Nat := 4983230072969 + 3 ^ 40 * 8374591 * 2
def baseEnd_8374591 : Nat := 4300190467817149107898463

theorem tailTrace_8374591 : CollatzResearch.WordTrace tailWord_8374591 prefixEnd_8374591 4300190467817149107898463 := by
  unfold tailWord_8374591
  simp only [CollatzResearch.WordTrace]
  refine ⟨305446427203294548118595627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203630951468863032079063751 305446427203294548118595627)
  ·
    refine ⟨458169640804941822177893441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305446427203294548118595627 458169640804941822177893441)
    ·
      refine ⟨343627230603706366633420081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458169640804941822177893441 343627230603706366633420081)
      ·
        refine ⟨257720422952779774975065061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343627230603706366633420081 257720422952779774975065061)
        ·
          refine ⟨48322579303646207807824699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257720422952779774975065061 48322579303646207807824699)
          ·
            refine ⟨72483868955469311711737049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48322579303646207807824699 72483868955469311711737049)
            ·
              refine ⟨54362901716601983783802787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72483868955469311711737049 54362901716601983783802787)
              ·
                refine ⟨81544352574902975675704181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54362901716601983783802787 81544352574902975675704181)
                ·
                  refine ⟨7644783053897153969597267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81544352574902975675704181 7644783053897153969597267)
                  ·
                    refine ⟨11467174580845730954395901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7644783053897153969597267 11467174580845730954395901)
                    ·
                      refine ⟨4300190467817149107898463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11467174580845730954395901 4300190467817149107898463)
                      ·
                        rfl

theorem cell23_8374591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_8374591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374591 prefixEnd_8374591 := by exact prefixLift 8374591
  have htrace : WordTrace (prefixWord ++ tailWord_8374591) baseStart_8374591 baseEnd_8374591 := by
    simpa [prefixWord, tailWord_8374591, baseEnd_8374591] using wordTrace_append hprefix tailTrace_8374591
  have hstable : (prefixWord ++ tailWord_8374591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374591).length < 2 ^ (prefixWord ++ tailWord_8374591).sum := by decide
  have hdescent : baseEnd_8374591 < baseStart_8374591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374631 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_8374631 : Nat := 118140960795 + 8374631 * 2 ^ 59
def prefixEnd_8374631 : Nat := 4983230072969 + 3 ^ 40 * 8374631 * 2
def baseEnd_8374631 : Nat := 4300211007043328951398279

theorem tailTrace_8374631 : CollatzResearch.WordTrace tailWord_8374631 prefixEnd_8374631 4300211007043328951398279 := by
  unfold tailWord_8374631
  simp only [CollatzResearch.WordTrace]
  refine ⟨305447886123149634950051747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203631924082099756633367831 305447886123149634950051747)
  ·
    refine ⟨458171829184724452425077621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305447886123149634950051747 458171829184724452425077621)
    ·
      refine ⟨42953608986067917414851027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458171829184724452425077621 42953608986067917414851027)
      ·
        refine ⟨64430413479101876122276541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42953608986067917414851027 64430413479101876122276541)
        ·
          refine ⟨24161405054663203545853703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64430413479101876122276541 24161405054663203545853703)
          ·
            refine ⟨36242107581994805318780555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161405054663203545853703 36242107581994805318780555)
            ·
              refine ⟨54363161372992207978170833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36242107581994805318780555 54363161372992207978170833)
              ·
                refine ⟨40772371029744155983628125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54363161372992207978170833 40772371029744155983628125)
                ·
                  refine ⟨15289639136154058493860547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40772371029744155983628125 15289639136154058493860547)
                  ·
                    refine ⟨22934458704231087740790821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15289639136154058493860547 22934458704231087740790821)
                    ·
                      refine ⟨4300211007043328951398279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22934458704231087740790821 4300211007043328951398279)
                      ·
                        rfl

theorem cell23_8374631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_8374631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374631 prefixEnd_8374631 := by exact prefixLift 8374631
  have htrace : WordTrace (prefixWord ++ tailWord_8374631) baseStart_8374631 baseEnd_8374631 := by
    simpa [prefixWord, tailWord_8374631, baseEnd_8374631] using wordTrace_append hprefix tailTrace_8374631
  have hstable : (prefixWord ++ tailWord_8374631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374631).length < 2 ^ (prefixWord ++ tailWord_8374631).sum := by decide
  have hdescent : baseEnd_8374631 < baseStart_8374631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374651 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3]
def baseStart_8374651 : Nat := 118140960795 + 8374651 * 2 ^ 59
def prefixEnd_8374651 : Nat := 4983230072969 + 3 ^ 40 * 8374651 * 2
def baseEnd_8374651 : Nat := 4300221276656418873148187

theorem tailTrace_8374651 : CollatzResearch.WordTrace tailWord_8374651 prefixEnd_8374651 4300221276656418873148187 := by
  unfold tailWord_8374651
  simp only [CollatzResearch.WordTrace]
  refine ⟨305448615583077178365779807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203632410388718118910519871 305448615583077178365779807)
  ·
    refine ⟨458172923374615767548669711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305448615583077178365779807 458172923374615767548669711)
    ·
      refine ⟨687259385061923651323004567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458172923374615767548669711 687259385061923651323004567)
      ·
        refine ⟨1030889077592885476984506851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687259385061923651323004567 1030889077592885476984506851)
        ·
          refine ⟨1546333616389328215476760277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030889077592885476984506851 1546333616389328215476760277)
          ·
            refine ⟨36242194134124880050236569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1546333616389328215476760277 36242194134124880050236569)
            ·
              refine ⟨27181645600593660037677427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36242194134124880050236569 27181645600593660037677427)
              ·
                refine ⟨40772468400890490056516141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27181645600593660037677427 40772468400890490056516141)
                ·
                  refine ⟨15289675650333933771193553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40772468400890490056516141 15289675650333933771193553)
                  ·
                    refine ⟨11467256737750450328395165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15289675650333933771193553 11467256737750450328395165)
                    ·
                      refine ⟨4300221276656418873148187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11467256737750450328395165 4300221276656418873148187)
                      ·
                        rfl

theorem cell23_8374651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 3].length) (baseStart_8374651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374651 prefixEnd_8374651 := by exact prefixLift 8374651
  have htrace : WordTrace (prefixWord ++ tailWord_8374651) baseStart_8374651 baseEnd_8374651 := by
    simpa [prefixWord, tailWord_8374651, baseEnd_8374651] using wordTrace_append hprefix tailTrace_8374651
  have hstable : (prefixWord ++ tailWord_8374651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374651).length < 2 ^ (prefixWord ++ tailWord_8374651).sum := by decide
  have hdescent : baseEnd_8374651 < baseStart_8374651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374665 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 1, 1, 4]
def baseStart_8374665 : Nat := 118140960795 + 8374665 * 2 ^ 59
def prefixEnd_8374665 : Nat := 4983230072969 + 3 ^ 40 * 8374665 * 2
def baseEnd_8374665 : Nat := 4300228465385581818373123

theorem tailTrace_8374665 : CollatzResearch.WordTrace tailWord_8374665 prefixEnd_8374665 4300228465385581818373123 := by
  unfold tailWord_8374665
  simp only [CollatzResearch.WordTrace]
  refine ⟨305449126205026458756789449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203632750803350972504526299 305449126205026458756789449)
  ·
    refine ⟨229086844653769844067592087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305449126205026458756789449 229086844653769844067592087)
    ·
      refine ⟨343630266980654766101388131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229086844653769844067592087 343630266980654766101388131)
      ·
        refine ⟨515445400470982149152082197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343630266980654766101388131 515445400470982149152082197)
        ·
          refine ⟨24161503147077288241503853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 515445400470982149152082197 24161503147077288241503853)
          ·
            refine ⟨9060563680153983090563945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24161503147077288241503853 9060563680153983090563945)
            ·
              refine ⟨6795422760115487317922959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9060563680153983090563945 6795422760115487317922959)
              ·
                refine ⟨10193134140173230976884439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795422760115487317922959 10193134140173230976884439)
                ·
                  refine ⟨15289701210259846465326659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193134140173230976884439 15289701210259846465326659)
                  ·
                    refine ⟨22934551815389769697989989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15289701210259846465326659 22934551815389769697989989)
                    ·
                      refine ⟨4300228465385581818373123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22934551815389769697989989 4300228465385581818373123)
                      ·
                        rfl

theorem cell23_8374665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 1, 4].length) (baseStart_8374665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374665 prefixEnd_8374665 := by exact prefixLift 8374665
  have htrace : WordTrace (prefixWord ++ tailWord_8374665) baseStart_8374665 baseEnd_8374665 := by
    simpa [prefixWord, tailWord_8374665, baseEnd_8374665] using wordTrace_append hprefix tailTrace_8374665
  have hstable : (prefixWord ++ tailWord_8374665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374665).length < 2 ^ (prefixWord ++ tailWord_8374665).sum := by decide
  have hdescent : baseEnd_8374665 < baseStart_8374665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374668 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_8374668 : Nat := 118140960795 + 8374668 * 2 ^ 59
def prefixEnd_8374668 : Nat := 4983230072969 + 3 ^ 40 * 8374668 * 2
def baseEnd_8374668 : Nat := 4300230005827545306635609

theorem tailTrace_8374668 : CollatzResearch.WordTrace tailWord_8374668 prefixEnd_8374668 4300230005827545306635609 := by
  unfold tailWord_8374668
  simp only [CollatzResearch.WordTrace]
  refine ⟨152724617812007795134574329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203632823749343726846099105 152724617812007795134574329)
  ·
    refine ⟨114543463359005846350930747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152724617812007795134574329 114543463359005846350930747)
    ·
      refine ⟨171815195038508769526396121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114543463359005846350930747 171815195038508769526396121)
      ·
        refine ⟨128861396278881577144797091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171815195038508769526396121 128861396278881577144797091)
        ·
          refine ⟨193292094418322365717195637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128861396278881577144797091 193292094418322365717195637)
          ·
            refine ⟨18121133851717721785987091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193292094418322365717195637 18121133851717721785987091)
            ·
              refine ⟨27181700777576582678980637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18121133851717721785987091 27181700777576582678980637)
              ·
                refine ⟨10193137791591218504617739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27181700777576582678980637 10193137791591218504617739)
                ·
                  refine ⟨15289706687386827756926609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193137791591218504617739 15289706687386827756926609)
                  ·
                    refine ⟨11467280015540120817694957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15289706687386827756926609 11467280015540120817694957)
                    ·
                      refine ⟨4300230005827545306635609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11467280015540120817694957 4300230005827545306635609)
                      ·
                        rfl

theorem cell23_8374668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_8374668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374668 prefixEnd_8374668 := by exact prefixLift 8374668
  have htrace : WordTrace (prefixWord ++ tailWord_8374668) baseStart_8374668 baseEnd_8374668 := by
    simpa [prefixWord, tailWord_8374668, baseEnd_8374668] using wordTrace_append hprefix tailTrace_8374668
  have hstable : (prefixWord ++ tailWord_8374668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374668).length < 2 ^ (prefixWord ++ tailWord_8374668).sum := by decide
  have hdescent : baseEnd_8374668 < baseStart_8374668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374682 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2]
def baseStart_8374682 : Nat := 118140960795 + 8374682 * 2 ^ 59
def prefixEnd_8374682 : Nat := 4983230072969 + 3 ^ 40 * 8374682 * 2
def baseEnd_8374682 : Nat := 4300237194556708251860545

theorem tailTrace_8374682 : CollatzResearch.WordTrace tailWord_8374682 prefixEnd_8374682 4300237194556708251860545 := by
  unfold tailWord_8374682
  simp only [CollatzResearch.WordTrace]
  refine ⟨76362436561491217665039575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203633164163976580440105533 76362436561491217665039575)
  ·
    refine ⟨114543654842236826497559363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76362436561491217665039575 114543654842236826497559363)
    ·
      refine ⟨171815482263355239746339045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114543654842236826497559363 171815482263355239746339045)
      ·
        refine ⟨32215402924379107452438571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171815482263355239746339045 32215402924379107452438571)
        ·
          refine ⟨48323104386568661178657857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32215402924379107452438571 48323104386568661178657857)
          ·
            refine ⟨36242328289926495883993393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48323104386568661178657857 36242328289926495883993393)
            ·
              refine ⟨27181746217444871912995045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36242328289926495883993393 27181746217444871912995045)
              ·
                refine ⟨5096577415770913483686571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27181746217444871912995045 5096577415770913483686571)
                ·
                  refine ⟨7644866123656370225529857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096577415770913483686571 7644866123656370225529857)
                  ·
                    refine ⟨5733649592742277669147393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7644866123656370225529857 5733649592742277669147393)
                    ·
                      refine ⟨4300237194556708251860545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733649592742277669147393 4300237194556708251860545)
                      ·
                        rfl

theorem cell23_8374682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_8374682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374682 prefixEnd_8374682 := by exact prefixLift 8374682
  have htrace : WordTrace (prefixWord ++ tailWord_8374682) baseStart_8374682 baseEnd_8374682 := by
    simpa [prefixWord, tailWord_8374682, baseEnd_8374682] using wordTrace_append hprefix tailTrace_8374682
  have hstable : (prefixWord ++ tailWord_8374682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374682).length < 2 ^ (prefixWord ++ tailWord_8374682).sum := by decide
  have hdescent : baseEnd_8374682 < baseStart_8374682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374704 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_8374704 : Nat := 118140960795 + 8374704 * 2 ^ 59
def prefixEnd_8374704 : Nat := 4983230072969 + 3 ^ 40 * 8374704 * 2
def baseEnd_8374704 : Nat := 4300248491131107165785443

theorem tailTrace_8374704 : CollatzResearch.WordTrace tailWord_8374704 prefixEnd_8374704 4300248491131107165785443 := by
  unfold tailWord_8374704
  simp only [CollatzResearch.WordTrace]
  refine ⟨152725274325942584208729583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203633699101256778944972777 152725274325942584208729583)
  ·
    refine ⟨229087911488913876313094375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152725274325942584208729583 229087911488913876313094375)
    ·
      refine ⟨343631867233370814469641563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229087911488913876313094375 343631867233370814469641563)
      ·
        refine ⟨515447800850056221704462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343631867233370814469641563 515447800850056221704462345)
        ·
          refine ⟨386585850637542166278346759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515447800850056221704462345 386585850637542166278346759)
          ·
            refine ⟨579878775956313249417520139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386585850637542166278346759 579878775956313249417520139)
            ·
              refine ⟨869818163934469874126280209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579878775956313249417520139 869818163934469874126280209)
              ·
                refine ⟨652363622950852405594710157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869818163934469874126280209 652363622950852405594710157)
                ·
                  refine ⟨244636358606569652098016309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652363622950852405594710157 244636358606569652098016309)
                  ·
                    refine ⟨22934658619365904884189029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244636358606569652098016309 22934658619365904884189029)
                    ·
                      refine ⟨4300248491131107165785443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22934658619365904884189029 4300248491131107165785443)
                      ·
                        rfl

theorem cell23_8374704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_8374704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374704 prefixEnd_8374704 := by exact prefixLift 8374704
  have htrace : WordTrace (prefixWord ++ tailWord_8374704) baseStart_8374704 baseEnd_8374704 := by
    simpa [prefixWord, tailWord_8374704, baseEnd_8374704] using wordTrace_append hprefix tailTrace_8374704
  have hstable : (prefixWord ++ tailWord_8374704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374704).length < 2 ^ (prefixWord ++ tailWord_8374704).sum := by decide
  have hdescent : baseEnd_8374704 < baseStart_8374704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374714 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_8374714 : Nat := 118140960795 + 8374714 * 2 ^ 59
def prefixEnd_8374714 : Nat := 4983230072969 + 3 ^ 40 * 8374714 * 2
def baseEnd_8374714 : Nat := 1433417875312550708886799

theorem tailTrace_8374714 : CollatzResearch.WordTrace tailWord_8374714 prefixEnd_8374714 1433417875312550708886799 := by
  unfold tailWord_8374714
  simp only [CollatzResearch.WordTrace]
  refine ⟨76362728345462235031330799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203633942254565960083548797 76362728345462235031330799)
  ·
    refine ⟨114544092518193352546996199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76362728345462235031330799 114544092518193352546996199)
    ·
      refine ⟨171816138777290028820494299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114544092518193352546996199 171816138777290028820494299)
      ·
        refine ⟨257724208165935043230741449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171816138777290028820494299 257724208165935043230741449)
        ·
          refine ⟨193293156124451282423056087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257724208165935043230741449 193293156124451282423056087)
          ·
            refine ⟨289939734186676923634584131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193293156124451282423056087 289939734186676923634584131)
            ·
              refine ⟨434909601280015385451876197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289939734186676923634584131 434909601280015385451876197)
              ·
                refine ⟨81545550240002884772226787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434909601280015385451876197 81545550240002884772226787)
                ·
                  refine ⟨122318325360004327158340181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81545550240002884772226787 122318325360004327158340181)
                  ·
                    refine ⟨1433417875312550708886799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122318325360004327158340181 1433417875312550708886799)
                    ·
                      rfl

theorem cell23_8374714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_8374714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374714 prefixEnd_8374714 := by exact prefixLift 8374714
  have htrace : WordTrace (prefixWord ++ tailWord_8374714) baseStart_8374714 baseEnd_8374714 := by
    simpa [prefixWord, tailWord_8374714, baseEnd_8374714] using wordTrace_append hprefix tailTrace_8374714
  have hstable : (prefixWord ++ tailWord_8374714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374714).length < 2 ^ (prefixWord ++ tailWord_8374714).sum := by decide
  have hdescent : baseEnd_8374714 < baseStart_8374714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374795 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 5]
def baseStart_8374795 : Nat := 118140960795 + 8374795 * 2 ^ 59
def prefixEnd_8374795 : Nat := 4983230072969 + 3 ^ 40 * 8374795 * 2
def baseEnd_8374795 : Nat := 477810579763407367749725

theorem tailTrace_8374795 : CollatzResearch.WordTrace tailWord_8374795 prefixEnd_8374795 477810579763407367749725 := by
  unfold tailWord_8374795
  simp only [CollatzResearch.WordTrace]
  refine ⟨305453867694555490959021839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203635911796370327306014559 305453867694555490959021839)
  ·
    refine ⟨458180801541833236438532759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305453867694555490959021839 458180801541833236438532759)
    ·
      refine ⟨687271202312749854657799139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458180801541833236438532759 687271202312749854657799139)
      ·
        refine ⟨1030906803469124781986698709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687271202312749854657799139 1030906803469124781986698709)
        ·
          refine ⟨24161878206307612077813251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1030906803469124781986698709 24161878206307612077813251)
          ·
            refine ⟨36242817309461418116719877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161878206307612077813251 36242817309461418116719877)
            ·
              refine ⟨6795528245524015896884977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36242817309461418116719877 6795528245524015896884977)
              ·
                refine ⟨5096646184143011922663733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795528245524015896884977 5096646184143011922663733)
                ·
                  refine ⟨477810579763407367749725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5096646184143011922663733 477810579763407367749725)
                  ·
                    rfl

theorem cell23_8374795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 5].length) (baseStart_8374795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374795 prefixEnd_8374795 := by exact prefixLift 8374795
  have htrace : WordTrace (prefixWord ++ tailWord_8374795) baseStart_8374795 baseEnd_8374795 := by
    simpa [prefixWord, tailWord_8374795, baseEnd_8374795] using wordTrace_append hprefix tailTrace_8374795
  have hstable : (prefixWord ++ tailWord_8374795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374795).length < 2 ^ (prefixWord ++ tailWord_8374795).sum := by decide
  have hdescent : baseEnd_8374795 < baseStart_8374795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374841 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_8374841 : Nat := 118140960795 + 8374841 * 2 ^ 59
def prefixEnd_8374841 : Nat := 4983230072969 + 3 ^ 40 * 8374841 * 2
def baseEnd_8374841 : Nat := 4300318837980773129772313

theorem tailTrace_8374841 : CollatzResearch.WordTrace tailWord_8374841 prefixEnd_8374841 4300318837980773129772313 := by
  unfold tailWord_8374841
  simp only [CollatzResearch.WordTrace]
  refine ⟨305455545452388840815196377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203637030301592560543464251 305455545452388840815196377)
  ·
    refine ⟨229091659089291630611397283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305455545452388840815196377 229091659089291630611397283)
    ·
      refine ⟨343637488633937445917095925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229091659089291630611397283 343637488633937445917095925)
      ·
        refine ⟨32216014559431635554727743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343637488633937445917095925 32216014559431635554727743)
        ·
          refine ⟨48324021839147453332091615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32216014559431635554727743 48324021839147453332091615)
          ·
            refine ⟨72486032758721179998137423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48324021839147453332091615 72486032758721179998137423)
            ·
              refine ⟨108729049138081769997206135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72486032758721179998137423 108729049138081769997206135)
              ·
                refine ⟨163093573707122654995809203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108729049138081769997206135 163093573707122654995809203)
                ·
                  refine ⟨244640360560683982493713805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163093573707122654995809203 244640360560683982493713805)
                  ·
                    refine ⟨91740135210256493435142677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244640360560683982493713805 91740135210256493435142677)
                    ·
                      refine ⟨4300318837980773129772313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91740135210256493435142677 4300318837980773129772313)
                      ·
                        rfl

theorem cell23_8374841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_8374841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374841 prefixEnd_8374841 := by exact prefixLift 8374841
  have htrace : WordTrace (prefixWord ++ tailWord_8374841) baseStart_8374841 baseEnd_8374841 := by
    simpa [prefixWord, tailWord_8374841, baseEnd_8374841] using wordTrace_append hprefix tailTrace_8374841
  have hstable : (prefixWord ++ tailWord_8374841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374841).length < 2 ^ (prefixWord ++ tailWord_8374841).sum := by decide
  have hdescent : baseEnd_8374841 < baseStart_8374841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374845 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_8374845 : Nat := 118140960795 + 8374845 * 2 ^ 59
def prefixEnd_8374845 : Nat := 4983230072969 + 3 ^ 40 * 8374845 * 2
def baseEnd_8374845 : Nat := 4300320891903391114122295

theorem tailTrace_8374845 : CollatzResearch.WordTrace tailWord_8374845 prefixEnd_8374845 4300320891903391114122295 := by
  unfold tailWord_8374845
  simp only [CollatzResearch.WordTrace]
  refine ⟨305455691344374349498341989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203637127562916232998894659 305455691344374349498341989)
  ·
    refine ⟨57272942127070190530939123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305455691344374349498341989 57272942127070190530939123)
    ·
      refine ⟨85909413190605285796408685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57272942127070190530939123 85909413190605285796408685)
      ·
        refine ⟨32216029946476982173653257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85909413190605285796408685 32216029946476982173653257)
        ·
          refine ⟨24162022459857736630239943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32216029946476982173653257 24162022459857736630239943)
          ·
            refine ⟨36243033689786604945359915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24162022459857736630239943 36243033689786604945359915)
            ·
              refine ⟨54364550534679907418039873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36243033689786604945359915 54364550534679907418039873)
              ·
                refine ⟨40773412901009930563529905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54364550534679907418039873 40773412901009930563529905)
                ·
                  refine ⟨30580059675757447922647429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40773412901009930563529905 30580059675757447922647429)
                  ·
                    refine ⟨5733761189204521485496393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30580059675757447922647429 5733761189204521485496393)
                    ·
                      refine ⟨4300320891903391114122295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733761189204521485496393 4300320891903391114122295)
                      ·
                        rfl

theorem cell23_8374845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_8374845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374845 prefixEnd_8374845 := by exact prefixLift 8374845
  have htrace : WordTrace (prefixWord ++ tailWord_8374845) baseStart_8374845 baseEnd_8374845 := by
    simpa [prefixWord, tailWord_8374845, baseEnd_8374845] using wordTrace_append hprefix tailTrace_8374845
  have hstable : (prefixWord ++ tailWord_8374845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374845).length < 2 ^ (prefixWord ++ tailWord_8374845).sum := by decide
  have hdescent : baseEnd_8374845 < baseStart_8374845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374848 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_8374848 : Nat := 118140960795 + 8374848 * 2 ^ 59
def prefixEnd_8374848 : Nat := 4983230072969 + 3 ^ 40 * 8374848 * 2
def baseEnd_8374848 : Nat := 4300322432345354602384781

theorem tailTrace_8374848 : CollatzResearch.WordTrace tailWord_8374848 prefixEnd_8374848 4300322432345354602384781 := by
  unfold tailWord_8374848
  simp only [CollatzResearch.WordTrace]
  refine ⟨152727900381681740505350599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203637200508908987340467465 152727900381681740505350599)
  ·
    refine ⟨229091850572522610758025899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152727900381681740505350599 229091850572522610758025899)
    ·
      refine ⟨343637775858783916137038849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229091850572522610758025899 343637775858783916137038849)
      ·
        refine ⟨257728331894087937102779137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343637775858783916137038849 257728331894087937102779137)
        ·
          refine ⟨193296248920565952827084353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257728331894087937102779137 193296248920565952827084353)
          ·
            refine ⟨144972186690424464620313265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193296248920565952827084353 144972186690424464620313265)
            ·
              refine ⟨108729140017818348465234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144972186690424464620313265 108729140017818348465234949)
              ·
                refine ⟨20386713753340940337231553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108729140017818348465234949 20386713753340940337231553)
                ·
                  refine ⟨15290035315005705252923665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20386713753340940337231553 15290035315005705252923665)
                  ·
                    refine ⟨11467526486254278939692749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15290035315005705252923665 11467526486254278939692749)
                    ·
                      refine ⟨4300322432345354602384781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11467526486254278939692749 4300322432345354602384781)
                      ·
                        rfl

theorem cell23_8374848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_8374848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374848 prefixEnd_8374848 := by exact prefixLift 8374848
  have htrace : WordTrace (prefixWord ++ tailWord_8374848) baseStart_8374848 baseEnd_8374848 := by
    simpa [prefixWord, tailWord_8374848, baseEnd_8374848] using wordTrace_append hprefix tailTrace_8374848
  have hstable : (prefixWord ++ tailWord_8374848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374848).length < 2 ^ (prefixWord ++ tailWord_8374848).sum := by decide
  have hdescent : baseEnd_8374848 < baseStart_8374848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374855 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 3, 4]
def baseStart_8374855 : Nat := 118140960795 + 8374855 * 2 ^ 59
def prefixEnd_8374855 : Nat := 4983230072969 + 3 ^ 40 * 8374855 * 2
def baseEnd_8374855 : Nat := 1433442008903312024999083

theorem tailTrace_8374855 : CollatzResearch.WordTrace tailWord_8374855 prefixEnd_8374855 1433442008903312024999083 := by
  unfold tailWord_8374855
  simp only [CollatzResearch.WordTrace]
  refine ⟨305456056074338121206206019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203637370716225414137470679 305456056074338121206206019)
  ·
    refine ⟨458184084111507181809309029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305456056074338121206206019 458184084111507181809309029)
    ·
      refine ⟨85909515770907596589245443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458184084111507181809309029 85909515770907596589245443)
      ·
        refine ⟨128864273656361394883868165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85909515770907596589245443 128864273656361394883868165)
        ·
          refine ⟨24162051310567761540725281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128864273656361394883868165 24162051310567761540725281)
          ·
            refine ⟨18121538482925821155543961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24162051310567761540725281 18121538482925821155543961)
            ·
              refine ⟨13591153862194365866657971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18121538482925821155543961 13591153862194365866657971)
              ·
                refine ⟨20386730793291548799986957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591153862194365866657971 20386730793291548799986957)
                ·
                  refine ⟨7645024047484330799995109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20386730793291548799986957 7645024047484330799995109)
                  ·
                    refine ⟨1433442008903312024999083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7645024047484330799995109 1433442008903312024999083)
                    ·
                      rfl

theorem cell23_8374855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_8374855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374855 prefixEnd_8374855 := by exact prefixLift 8374855
  have htrace : WordTrace (prefixWord ++ tailWord_8374855) baseStart_8374855 baseEnd_8374855 := by
    simpa [prefixWord, tailWord_8374855, baseEnd_8374855] using wordTrace_append hprefix tailTrace_8374855
  have hstable : (prefixWord ++ tailWord_8374855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374855).length < 2 ^ (prefixWord ++ tailWord_8374855).sum := by decide
  have hdescent : baseEnd_8374855 < baseStart_8374855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374871 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_8374871 : Nat := 118140960795 + 8374871 * 2 ^ 59
def prefixEnd_8374871 : Nat := 4983230072969 + 3 ^ 40 * 8374871 * 2
def baseEnd_8374871 : Nat := 4300334242400408012397175

theorem tailTrace_8374871 : CollatzResearch.WordTrace tailWord_8374871 prefixEnd_8374871 4300334242400408012397175 := by
  unfold tailWord_8374871
  simp only [CollatzResearch.WordTrace]
  refine ⟨305456639642280155938788467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203637759761520103959192311 305456639642280155938788467)
  ·
    refine ⟨458184959463420233908182701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305456639642280155938788467 458184959463420233908182701)
    ·
      refine ⟨171819359798782587715568513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458184959463420233908182701 171819359798782587715568513)
      ·
        refine ⟨128864519849086940786676385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171819359798782587715568513 128864519849086940786676385)
        ·
          refine ⟨96648389886815205590007289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128864519849086940786676385 96648389886815205590007289)
          ·
            refine ⟨72486292415111404192505467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96648389886815205590007289 72486292415111404192505467)
            ·
              refine ⟨108729438622667106288758201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72486292415111404192505467 108729438622667106288758201)
              ·
                refine ⟨81547078967000329716568651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108729438622667106288758201 81547078967000329716568651)
                ·
                  refine ⟨122320618450500494574852977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81547078967000329716568651 122320618450500494574852977)
                  ·
                    refine ⟨91740463837875370931139733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122320618450500494574852977 91740463837875370931139733)
                    ·
                      refine ⟨4300334242400408012397175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91740463837875370931139733 4300334242400408012397175)
                      ·
                        rfl

theorem cell23_8374871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_8374871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374871 prefixEnd_8374871 := by exact prefixLift 8374871
  have htrace : WordTrace (prefixWord ++ tailWord_8374871) baseStart_8374871 baseEnd_8374871 := by
    simpa [prefixWord, tailWord_8374871, baseEnd_8374871] using wordTrace_append hprefix tailTrace_8374871
  have hstable : (prefixWord ++ tailWord_8374871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374871).length < 2 ^ (prefixWord ++ tailWord_8374871).sum := by decide
  have hdescent : baseEnd_8374871 < baseStart_8374871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374905 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 4, 3, 2]
def baseStart_8374905 : Nat := 118140960795 + 8374905 * 2 ^ 59
def prefixEnd_8374905 : Nat := 4983230072969 + 3 ^ 40 * 8374905 * 2
def baseEnd_8374905 : Nat := 4300351700742660879372019

theorem tailTrace_8374905 : CollatzResearch.WordTrace tailWord_8374905 prefixEnd_8374905 4300351700742660879372019 := by
  unfold tailWord_8374905
  simp only [CollatzResearch.WordTrace]
  refine ⟨305457879724156979745526169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203638586482771319830350779 305457879724156979745526169)
  ·
    refine ⟨229093409793117734809144627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305457879724156979745526169 229093409793117734809144627)
    ·
      refine ⟨343640114689676602213716941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229093409793117734809144627 343640114689676602213716941)
      ·
        refine ⟨128865043008628725830143853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343640114689676602213716941 128865043008628725830143853)
        ·
          refine ⟨48324391128235772186303945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128865043008628725830143853 48324391128235772186303945)
          ·
            refine ⟨36243293346176829139727959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48324391128235772186303945 36243293346176829139727959)
            ·
              refine ⟨54364940019265243709591939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36243293346176829139727959 54364940019265243709591939)
              ·
                refine ⟨81547410028897865564387909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54364940019265243709591939 81547410028897865564387909)
                ·
                  refine ⟨15290139380418349793322733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81547410028897865564387909 15290139380418349793322733)
                  ·
                    refine ⟨5733802267656881172496025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15290139380418349793322733 5733802267656881172496025)
                    ·
                      refine ⟨4300351700742660879372019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733802267656881172496025 4300351700742660879372019)
                      ·
                        rfl

theorem cell23_8374905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_8374905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374905 prefixEnd_8374905 := by exact prefixLift 8374905
  have htrace : WordTrace (prefixWord ++ tailWord_8374905) baseStart_8374905 baseEnd_8374905 := by
    simpa [prefixWord, tailWord_8374905, baseEnd_8374905] using wordTrace_append hprefix tailTrace_8374905
  have hstable : (prefixWord ++ tailWord_8374905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374905).length < 2 ^ (prefixWord ++ tailWord_8374905).sum := by decide
  have hdescent : baseEnd_8374905 < baseStart_8374905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 5, 6]
def baseStart_8374911 : Nat := 118140960795 + 8374911 * 2 ^ 59
def prefixEnd_8374911 : Nat := 4983230072969 + 3 ^ 40 * 8374911 * 2
def baseEnd_8374911 : Nat := 1433451593875529285298997

theorem tailTrace_8374911 : CollatzResearch.WordTrace tailWord_8374911 prefixEnd_8374911 1433451593875529285298997 := by
  unfold tailWord_8374911
  simp only [CollatzResearch.WordTrace]
  refine ⟨305458098562135242770244587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203638732374756828513496391 305458098562135242770244587)
  ·
    refine ⟨458187147843202864155366881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305458098562135242770244587 458187147843202864155366881)
    ·
      refine ⟨343640360882402148116525161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458187147843202864155366881 343640360882402148116525161)
      ·
        refine ⟨257730270661801611087393871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343640360882402148116525161 257730270661801611087393871)
        ·
          refine ⟨386595405992702416631090807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257730270661801611087393871 386595405992702416631090807)
          ·
            refine ⟨579893108989053624946636211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386595405992702416631090807 579893108989053624946636211)
            ·
              refine ⟨869839663483580437419954317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579893108989053624946636211 869839663483580437419954317)
              ·
                refine ⟨326189873806342664032482869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869839663483580437419954317 326189873806342664032482869)
                ·
                  refine ⟨30580300669344624753045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326189873806342664032482869 30580300669344624753045269)
                  ·
                    refine ⟨1433451593875529285298997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30580300669344624753045269 1433451593875529285298997)
                    ·
                      rfl

theorem cell23_8374911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_8374911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374911 prefixEnd_8374911 := by exact prefixLift 8374911
  have htrace : WordTrace (prefixWord ++ tailWord_8374911) baseStart_8374911 baseEnd_8374911 := by
    simpa [prefixWord, tailWord_8374911, baseEnd_8374911] using wordTrace_append hprefix tailTrace_8374911
  have hstable : (prefixWord ++ tailWord_8374911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374911).length < 2 ^ (prefixWord ++ tailWord_8374911).sum := by decide
  have hdescent : baseEnd_8374911 < baseStart_8374911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374912 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3]
def baseStart_8374912 : Nat := 118140960795 + 8374912 * 2 ^ 59
def prefixEnd_8374912 : Nat := 4983230072969 + 3 ^ 40 * 8374912 * 2
def baseEnd_8374912 : Nat := 4300355295107242351984487

theorem tailTrace_8374912 : CollatzResearch.WordTrace tailWord_8374912 prefixEnd_8374912 4300355295107242351984487 := by
  unfold tailWord_8374912
  simp only [CollatzResearch.WordTrace]
  refine ⟨152729067517565809970515495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203638756690087746627353993 152729067517565809970515495)
  ·
    refine ⟨229093601276348714955773243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152729067517565809970515495 229093601276348714955773243)
    ·
      refine ⟨343640401914523072433659865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229093601276348714955773243 343640401914523072433659865)
      ·
        refine ⟨257730301435892304325244899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343640401914523072433659865 257730301435892304325244899)
        ·
          refine ⟨386595452153838456487867349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257730301435892304325244899 386595452153838456487867349)
          ·
            refine ⟨9060830909855588823934391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 386595452153838456487867349 9060830909855588823934391)
            ·
              refine ⟨13591246364783383235901587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060830909855588823934391 13591246364783383235901587)
              ·
                refine ⟨20386869547175074853852381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591246364783383235901587 20386869547175074853852381)
                ·
                  refine ⟨7645076080190653070194643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20386869547175074853852381 7645076080190653070194643)
                  ·
                    refine ⟨11467614120285979605291965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7645076080190653070194643 11467614120285979605291965)
                    ·
                      refine ⟨4300355295107242351984487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11467614120285979605291965 4300355295107242351984487)
                      ·
                        rfl

theorem cell23_8374912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_8374912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374912 prefixEnd_8374912 := by exact prefixLift 8374912
  have htrace : WordTrace (prefixWord ++ tailWord_8374912) baseStart_8374912 baseEnd_8374912 := by
    simpa [prefixWord, tailWord_8374912, baseEnd_8374912] using wordTrace_append hprefix tailTrace_8374912
  have hstable : (prefixWord ++ tailWord_8374912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374912).length < 2 ^ (prefixWord ++ tailWord_8374912).sum := by decide
  have hdescent : baseEnd_8374912 < baseStart_8374912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374932 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_8374932 : Nat := 118140960795 + 8374932 * 2 ^ 59
def prefixEnd_8374932 : Nat := 4983230072969 + 3 ^ 40 * 8374932 * 2
def baseEnd_8374932 : Nat := 1433455188240110757911465

theorem tailTrace_8374932 : CollatzResearch.WordTrace tailWord_8374932 prefixEnd_8374932 1433455188240110757911465 := by
  unfold tailWord_8374932
  simp only [CollatzResearch.WordTrace]
  refine ⟨152729432247529581678379525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203639242996706108904506033 152729432247529581678379525)
  ·
    refine ⟨28636768546411796564696161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152729432247529581678379525 28636768546411796564696161)
    ·
      refine ⟨21477576409808847423522121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28636768546411796564696161 21477576409808847423522121)
      ·
        refine ⟨16108182307356635567641591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21477576409808847423522121 16108182307356635567641591)
        ·
          refine ⟨24162273461034953351462387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16108182307356635567641591 24162273461034953351462387)
          ·
            refine ⟨36243410191552430027193581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24162273461034953351462387 36243410191552430027193581)
            ·
              refine ⟨13591278821832161260197593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36243410191552430027193581 13591278821832161260197593)
              ·
                refine ⟨10193459116374120945148195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13591278821832161260197593 10193459116374120945148195)
                ·
                  refine ⟨15290188674561181417722293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193459116374120945148195 15290188674561181417722293)
                  ·
                    refine ⟨1433455188240110757911465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15290188674561181417722293 1433455188240110757911465)
                    ·
                      rfl

theorem cell23_8374932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_8374932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374932 prefixEnd_8374932 := by exact prefixLift 8374932
  have htrace : WordTrace (prefixWord ++ tailWord_8374932) baseStart_8374932 baseEnd_8374932 := by
    simpa [prefixWord, tailWord_8374932, baseEnd_8374932] using wordTrace_append hprefix tailTrace_8374932
  have hstable : (prefixWord ++ tailWord_8374932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374932).length < 2 ^ (prefixWord ++ tailWord_8374932).sum := by decide
  have hdescent : baseEnd_8374932 < baseStart_8374932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8374945 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_8374945 : Nat := 118140960795 + 8374945 * 2 ^ 59
def prefixEnd_8374945 : Nat := 4983230072969 + 3 ^ 40 * 8374945 * 2
def baseEnd_8374945 : Nat := 1433457413322946907623945

theorem tailTrace_8374945 : CollatzResearch.WordTrace tailWord_8374945 prefixEnd_8374945 1433457413322946907623945 := by
  unfold tailWord_8374945
  simp only [CollatzResearch.WordTrace]
  refine ⟨305459338644012066576982289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203639559096008044384654859 305459338644012066576982289)
  ·
    refine ⟨229094503983009049932736717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305459338644012066576982289 229094503983009049932736717)
    ·
      refine ⟨85910438993628393724776269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229094503983009049932736717 85910438993628393724776269)
      ·
        refine ⟨32216414622610647646791101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85910438993628393724776269 32216414622610647646791101)
        ·
          refine ⟨12081155483478992867546663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32216414622610647646791101 12081155483478992867546663)
          ·
            refine ⟨18121733225218489301319995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081155483478992867546663 18121733225218489301319995)
            ·
              refine ⟨27182599837827733951979993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18121733225218489301319995 27182599837827733951979993)
              ·
                refine ⟨20386949878370800463984995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27182599837827733951979993 20386949878370800463984995)
                ·
                  refine ⟨30580424817556200695977493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20386949878370800463984995 30580424817556200695977493)
                  ·
                    refine ⟨1433457413322946907623945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30580424817556200695977493 1433457413322946907623945)
                    ·
                      rfl

theorem cell23_8374945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_8374945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8374945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8374945 prefixEnd_8374945 := by exact prefixLift 8374945
  have htrace : WordTrace (prefixWord ++ tailWord_8374945) baseStart_8374945 baseEnd_8374945 := by
    simpa [prefixWord, tailWord_8374945, baseEnd_8374945] using wordTrace_append hprefix tailTrace_8374945
  have hstable : (prefixWord ++ tailWord_8374945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8374945).length < 2 ^ (prefixWord ++ tailWord_8374945).sum := by decide
  have hdescent : baseEnd_8374945 < baseStart_8374945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8374945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375065 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 5]
def baseStart_8375065 : Nat := 118140960795 + 8375065 * 2 ^ 59
def prefixEnd_8375065 : Nat := 4983230072969 + 3 ^ 40 * 8375065 * 2
def baseEnd_8375065 : Nat := 477825984183042250374587

theorem tailTrace_8375065 : CollatzResearch.WordTrace tailWord_8375065 prefixEnd_8375065 477825984183042250374587 := by
  unfold tailWord_8375065
  simp only [CollatzResearch.WordTrace]
  refine ⟨305463715403577327071350649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203642476935718218047567099 305463715403577327071350649)
  ·
    refine ⟨229097786552682995303512987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305463715403577327071350649 229097786552682995303512987)
    ·
      refine ⟨343646679829024492955269481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229097786552682995303512987 343646679829024492955269481)
      ·
        refine ⟨257735009871768369716452111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343646679829024492955269481 257735009871768369716452111)
        ·
          refine ⟨386602514807652554574678167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257735009871768369716452111 386602514807652554574678167)
          ·
            refine ⟨579903772211478831862017251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386602514807652554574678167 579903772211478831862017251)
            ·
              refine ⟨869855658317218247793025877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579903772211478831862017251 869855658317218247793025877)
              ·
                refine ⟨5096810497952450670662261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 869855658317218247793025877 5096810497952450670662261)
                ·
                  refine ⟨477825984183042250374587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5096810497952450670662261 477825984183042250374587)
                  ·
                    rfl

theorem cell23_8375065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 5].length) (baseStart_8375065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375065 prefixEnd_8375065 := by exact prefixLift 8375065
  have htrace : WordTrace (prefixWord ++ tailWord_8375065) baseStart_8375065 baseEnd_8375065 := by
    simpa [prefixWord, tailWord_8375065, baseEnd_8375065] using wordTrace_append hprefix tailTrace_8375065
  have hstable : (prefixWord ++ tailWord_8375065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375065).length < 2 ^ (prefixWord ++ tailWord_8375065).sum := by decide
  have hdescent : baseEnd_8375065 < baseStart_8375065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375093 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_8375093 : Nat := 118140960795 + 8375093 * 2 ^ 59
def prefixEnd_8375093 : Nat := 4983230072969 + 3 ^ 40 * 8375093 * 2
def baseEnd_8375093 : Nat := 4300448235105706143821155

theorem tailTrace_8375093 : CollatzResearch.WordTrace tailWord_8375093 prefixEnd_8375093 4300448235105706143821155 := by
  unfold tailWord_8375093
  simp only [CollatzResearch.WordTrace]
  refine ⟨305464736647475887853369933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203643157764983925235579955 305464736647475887853369933)
  ·
    refine ⟨114549276242803457945013725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305464736647475887853369933 114549276242803457945013725)
    ·
      refine ⟨42955978591051296729380147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114549276242803457945013725 42955978591051296729380147)
      ·
        refine ⟨64433967886576945094070221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42955978591051296729380147 64433967886576945094070221)
        ·
          refine ⟨24162737957466354410276333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64433967886576945094070221 24162737957466354410276333)
          ·
            refine ⟨9061026734049882903853625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24162737957466354410276333 9061026734049882903853625)
            ·
              refine ⟨6795770050537412177890219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9061026734049882903853625 6795770050537412177890219)
              ·
                refine ⟨10193655075806118266835329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795770050537412177890219 10193655075806118266835329)
                ·
                  refine ⟨7645241306854588700126497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10193655075806118266835329 7645241306854588700126497)
                  ·
                    refine ⟨5733930980140941525094873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645241306854588700126497 5733930980140941525094873)
                    ·
                      refine ⟨4300448235105706143821155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5733930980140941525094873 4300448235105706143821155)
                      ·
                        rfl

theorem cell23_8375093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_8375093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375093 prefixEnd_8375093 := by exact prefixLift 8375093
  have htrace : WordTrace (prefixWord ++ tailWord_8375093) baseStart_8375093 baseEnd_8375093 := by
    simpa [prefixWord, tailWord_8375093, baseEnd_8375093] using wordTrace_append hprefix tailTrace_8375093
  have hstable : (prefixWord ++ tailWord_8375093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375093).length < 2 ^ (prefixWord ++ tailWord_8375093).sum := by decide
  have hdescent : baseEnd_8375093 < baseStart_8375093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375155 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 6]
def baseStart_8375155 : Nat := 118140960795 + 8375155 * 2 ^ 59
def prefixEnd_8375155 : Nat := 4983230072969 + 3 ^ 40 * 8375155 * 2
def baseEnd_8375155 : Nat := 477831118989587211249541

theorem tailTrace_8375155 : CollatzResearch.WordTrace tailWord_8375155 prefixEnd_8375155 477831118989587211249541 := by
  unfold tailWord_8375155
  simp only [CollatzResearch.WordTrace]
  refine ⟨305466997973251272442126919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203644665315500848294751279 305466997973251272442126919)
  ·
    refine ⟨458200496959876908663190379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305466997973251272442126919 458200496959876908663190379)
    ·
      refine ⟨687300745439815362994785569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458200496959876908663190379 687300745439815362994785569)
      ·
        refine ⟨515475559079861522246089177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687300745439815362994785569 515475559079861522246089177)
        ·
          refine ⟨386606669309896141684566883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515475559079861522246089177 386606669309896141684566883)
          ·
            refine ⟨579910003964844212526850325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386606669309896141684566883 579910003964844212526850325)
            ·
              refine ⟨27183281435852072462196109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 579910003964844212526850325 27183281435852072462196109)
              ·
                refine ⟨10193730538444527173323541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27183281435852072462196109 10193730538444527173323541)
                ·
                  refine ⟨477831118989587211249541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10193730538444527173323541 477831118989587211249541)
                  ·
                    rfl

theorem cell23_8375155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 6].length) (baseStart_8375155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375155 prefixEnd_8375155 := by exact prefixLift 8375155
  have htrace : WordTrace (prefixWord ++ tailWord_8375155) baseStart_8375155 baseEnd_8375155 := by
    simpa [prefixWord, tailWord_8375155, baseEnd_8375155] using wordTrace_append hprefix tailTrace_8375155
  have hstable : (prefixWord ++ tailWord_8375155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375155).length < 2 ^ (prefixWord ++ tailWord_8375155).sum := by decide
  have hdescent : baseEnd_8375155 < baseStart_8375155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375176 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 1, 4]
def baseStart_8375176 : Nat := 118140960795 + 8375176 * 2 ^ 59
def prefixEnd_8375176 : Nat := 4983230072969 + 3 ^ 40 * 8375176 * 2
def baseEnd_8375176 : Nat := 1433496951333343106361091

theorem tailTrace_8375176 : CollatzResearch.WordTrace tailWord_8375176 prefixEnd_8375176 1433496951333343106361091 := by
  unfold tailWord_8375176
  simp only [CollatzResearch.WordTrace]
  refine ⟨152733881953087596514320691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203645175937450128685760921 152733881953087596514320691)
  ·
    refine ⟨229100822929631394771481037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152733881953087596514320691 229100822929631394771481037)
    ·
      refine ⟨85912808598611773039305389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229100822929631394771481037 85912808598611773039305389)
      ·
        refine ⟨32217303224479414889739521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85912808598611773039305389 32217303224479414889739521)
        ·
          refine ⟨24162977418359561167304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32217303224479414889739521 24162977418359561167304641)
          ·
            refine ⟨18122233063769670875478481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24162977418359561167304641 18122233063769670875478481)
            ·
              refine ⟨13591674797827253156608861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18122233063769670875478481 13591674797827253156608861)
              ·
                refine ⟨5096878049185219933728323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13591674797827253156608861 5096878049185219933728323)
                ·
                  refine ⟨7645317073777829900592485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096878049185219933728323 7645317073777829900592485)
                  ·
                    refine ⟨1433496951333343106361091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7645317073777829900592485 1433496951333343106361091)
                    ·
                      rfl

theorem cell23_8375176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_8375176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375176 prefixEnd_8375176 := by exact prefixLift 8375176
  have htrace : WordTrace (prefixWord ++ tailWord_8375176) baseStart_8375176 baseEnd_8375176 := by
    simpa [prefixWord, tailWord_8375176, baseEnd_8375176] using wordTrace_append hprefix tailTrace_8375176
  have hstable : (prefixWord ++ tailWord_8375176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375176).length < 2 ^ (prefixWord ++ tailWord_8375176).sum := by decide
  have hdescent : baseEnd_8375176 < baseStart_8375176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375199 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 3]
def baseStart_8375199 : Nat := 118140960795 + 8375199 * 2 ^ 59
def prefixEnd_8375199 : Nat := 4983230072969 + 3 ^ 40 * 8375199 * 2
def baseEnd_8375199 : Nat := 4300502664055082729095667

theorem tailTrace_8375199 : CollatzResearch.WordTrace tailWord_8375199 prefixEnd_8375199 4300502664055082729095667 := by
  unfold tailWord_8375199
  simp only [CollatzResearch.WordTrace]
  refine ⟨305468602785091867956728651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203645735190061245304485767 305468602785091867956728651)
  ·
    refine ⟨458202904177637801935092977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305468602785091867956728651 458202904177637801935092977)
    ·
      refine ⟨343652178133228351451319733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458202904177637801935092977 343652178133228351451319733)
      ·
        refine ⟨32217391699990157948561225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343652178133228351451319733 32217391699990157948561225)
        ·
          refine ⟨24163043774992618461420919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32217391699990157948561225 24163043774992618461420919)
          ·
            refine ⟨36244565662488927692131379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24163043774992618461420919 36244565662488927692131379)
            ·
              refine ⟨54366848493733391538197069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36244565662488927692131379 54366848493733391538197069)
              ·
                refine ⟨20387568185150021826823901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54366848493733391538197069 20387568185150021826823901)
                ·
                  refine ⟨7645338069431258185058963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20387568185150021826823901 7645338069431258185058963)
                  ·
                    refine ⟨11468007104146887277588445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7645338069431258185058963 11468007104146887277588445)
                    ·
                      refine ⟨4300502664055082729095667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468007104146887277588445 4300502664055082729095667)
                      ·
                        rfl

theorem cell23_8375199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_8375199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375199 prefixEnd_8375199 := by exact prefixLift 8375199
  have htrace : WordTrace (prefixWord ++ tailWord_8375199) baseStart_8375199 baseEnd_8375199 := by
    simpa [prefixWord, tailWord_8375199, baseEnd_8375199] using wordTrace_append hprefix tailTrace_8375199
  have hstable : (prefixWord ++ tailWord_8375199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375199).length < 2 ^ (prefixWord ++ tailWord_8375199).sum := by decide
  have hdescent : baseEnd_8375199 < baseStart_8375199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375215 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 1, 6]
def baseStart_8375215 : Nat := 118140960795 + 8375215 * 2 ^ 59
def prefixEnd_8375215 : Nat := 4983230072969 + 3 ^ 40 * 8375215 * 2
def baseEnd_8375215 : Nat := 1433503626581851555498531

theorem tailTrace_8375215 : CollatzResearch.WordTrace tailWord_8375215 prefixEnd_8375215 1433503626581851555498531 := by
  unfold tailWord_8375215
  simp only [CollatzResearch.WordTrace]
  refine ⟨305469186353033902689311099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203646124235355935126207399 305469186353033902689311099)
  ·
    refine ⟨458203779529550854033966649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305469186353033902689311099 458203779529550854033966649)
    ·
      refine ⟨343652834647163140525474987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458203779529550854033966649 343652834647163140525474987)
      ·
        refine ⟨515479251970744710788212481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343652834647163140525474987 515479251970744710788212481)
        ·
          refine ⟨386609438978058533091159361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515479251970744710788212481 386609438978058533091159361)
          ·
            refine ⟨289957079233543899818369521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386609438978058533091159361 289957079233543899818369521)
            ·
              refine ⟨217467809425157924863777141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289957079233543899818369521 217467809425157924863777141)
              ·
                refine ⟨20387607133608555455979107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217467809425157924863777141 20387607133608555455979107)
                ·
                  refine ⟨30581410700412833183968661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20387607133608555455979107 30581410700412833183968661)
                  ·
                    refine ⟨1433503626581851555498531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30581410700412833183968661 1433503626581851555498531)
                    ·
                      rfl

theorem cell23_8375215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_8375215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375215 prefixEnd_8375215 := by exact prefixLift 8375215
  have htrace : WordTrace (prefixWord ++ tailWord_8375215) baseStart_8375215 baseEnd_8375215 := by
    simpa [prefixWord, tailWord_8375215, baseEnd_8375215] using wordTrace_append hprefix tailTrace_8375215
  have hstable : (prefixWord ++ tailWord_8375215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375215).length < 2 ^ (prefixWord ++ tailWord_8375215).sum := by decide
  have hdescent : baseEnd_8375215 < baseStart_8375215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375232 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_8375232 : Nat := 118140960795 + 8375232 * 2 ^ 59
def prefixEnd_8375232 : Nat := 4983230072969 + 3 ^ 40 * 8375232 * 2
def baseEnd_8375232 : Nat := 1433506536305560366661005

theorem tailTrace_8375232 : CollatzResearch.WordTrace tailWord_8375232 prefixEnd_8375232 1433506536305560366661005 := by
  unfold tailWord_8375232
  simp only [CollatzResearch.WordTrace]
  refine ⟨152734903196986157296339975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203646537595981543061786633 152734903196986157296339975)
  ·
    refine ⟨229102354795479235944509963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152734903196986157296339975 229102354795479235944509963)
    ·
      refine ⟨343653532193218853916764945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229102354795479235944509963 343653532193218853916764945)
      ·
        refine ⟨257740149144914140437573709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343653532193218853916764945 257740149144914140437573709)
        ·
          refine ⟨96652555929342802664090141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257740149144914140437573709 96652555929342802664090141)
          ·
            refine ⟨36244708473503550999033803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96652555929342802664090141 36244708473503550999033803)
            ·
              refine ⟨54367062710255326498550705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36244708473503550999033803 54367062710255326498550705)
              ·
                refine ⟨40775297032691494873913029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54367062710255326498550705 40775297032691494873913029)
                ·
                  refine ⟨7645368193629655288858693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40775297032691494873913029 7645368193629655288858693)
                  ·
                    refine ⟨1433506536305560366661005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7645368193629655288858693 1433506536305560366661005)
                    ·
                      rfl

theorem cell23_8375232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_8375232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375232 prefixEnd_8375232 := by exact prefixLift 8375232
  have htrace : WordTrace (prefixWord ++ tailWord_8375232) baseStart_8375232 baseEnd_8375232 := by
    simpa [prefixWord, tailWord_8375232, baseEnd_8375232] using wordTrace_append hprefix tailTrace_8375232
  have hstable : (prefixWord ++ tailWord_8375232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375232).length < 2 ^ (prefixWord ++ tailWord_8375232).sum := by decide
  have hdescent : baseEnd_8375232 < baseStart_8375232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375239 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_8375239 : Nat := 118140960795 + 8375239 * 2 ^ 59
def prefixEnd_8375239 : Nat := 4983230072969 + 3 ^ 40 * 8375239 * 2
def baseEnd_8375239 : Nat := 4300523203281262572595483

theorem tailTrace_8375239 : CollatzResearch.WordTrace tailWord_8375239 prefixEnd_8375239 4300523203281262572595483 := by
  unfold tailWord_8375239
  simp only [CollatzResearch.WordTrace]
  refine ⟨305470061704946954788184771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203646707803297969858789847 305470061704946954788184771)
  ·
    refine ⟨458205092557420432182277157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305470061704946954788184771 458205092557420432182277157)
    ·
      refine ⟨85913454854516331034176967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458205092557420432182277157 85913454854516331034176967)
      ·
        refine ⟨128870182281774496551265451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85913454854516331034176967 128870182281774496551265451)
        ·
          refine ⟨193305273422661744826898177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128870182281774496551265451 193305273422661744826898177)
          ·
            refine ⟨144978955066996308620173633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193305273422661744826898177 144978955066996308620173633)
            ·
              refine ⟨108734216300247231465130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144978955066996308620173633 108734216300247231465130225)
              ·
                refine ⟨81550662225185423598847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108734216300247231465130225 81550662225185423598847669)
                ·
                  refine ⟨7645374583611133462391969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81550662225185423598847669 7645374583611133462391969)
                  ·
                    refine ⟨5734030937708350096793977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645374583611133462391969 5734030937708350096793977)
                    ·
                      refine ⟨4300523203281262572595483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734030937708350096793977 4300523203281262572595483)
                      ·
                        rfl

theorem cell23_8375239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_8375239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375239 prefixEnd_8375239 := by exact prefixLift 8375239
  have htrace : WordTrace (prefixWord ++ tailWord_8375239) baseStart_8375239 baseEnd_8375239 := by
    simpa [prefixWord, tailWord_8375239, baseEnd_8375239] using wordTrace_append hprefix tailTrace_8375239
  have hstable : (prefixWord ++ tailWord_8375239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375239).length < 2 ^ (prefixWord ++ tailWord_8375239).sum := by decide
  have hdescent : baseEnd_8375239 < baseStart_8375239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375242 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_8375242 : Nat := 118140960795 + 8375242 * 2 ^ 59
def prefixEnd_8375242 : Nat := 4983230072969 + 3 ^ 40 * 8375242 * 2
def baseEnd_8375242 : Nat := 4300524743723226060857969

theorem tailTrace_8375242 : CollatzResearch.WordTrace tailWord_8375242 prefixEnd_8375242 4300524743723226060857969 := by
  unfold tailWord_8375242
  simp only [CollatzResearch.WordTrace]
  refine ⟨76367542780984021575135995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203646780749290724200362653 76367542780984021575135995)
  ·
    refine ⟨114551314171476032362703993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76367542780984021575135995 114551314171476032362703993)
    ·
      refine ⟨85913485628607024272027995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114551314171476032362703993 85913485628607024272027995)
      ·
        refine ⟨128870228442910536408041993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85913485628607024272027995 128870228442910536408041993)
        ·
          refine ⟨96652671332182902306031495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128870228442910536408041993 96652671332182902306031495)
          ·
            refine ⟨144979006998274353459047243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96652671332182902306031495 144979006998274353459047243)
            ·
              refine ⟨217468510497411530188570865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144979006998274353459047243 217468510497411530188570865)
              ·
                refine ⟨163101382873058647641428149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217468510497411530188570865 163101382873058647641428149)
                ·
                  refine ⟨15290754644349248216383889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163101382873058647641428149 15290754644349248216383889)
                  ·
                    refine ⟨11468065983261936162287917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15290754644349248216383889 11468065983261936162287917)
                    ·
                      refine ⟨4300524743723226060857969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468065983261936162287917 4300524743723226060857969)
                      ·
                        rfl

theorem cell23_8375242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_8375242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375242 prefixEnd_8375242 := by exact prefixLift 8375242
  have htrace : WordTrace (prefixWord ++ tailWord_8375242) baseStart_8375242 baseEnd_8375242 := by
    simpa [prefixWord, tailWord_8375242, baseEnd_8375242] using wordTrace_append hprefix tailTrace_8375242
  have hstable : (prefixWord ++ tailWord_8375242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375242).length < 2 ^ (prefixWord ++ tailWord_8375242).sum := by decide
  have hdescent : baseEnd_8375242 < baseStart_8375242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375250 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_8375250 : Nat := 118140960795 + 8375250 * 2 ^ 59
def prefixEnd_8375250 : Nat := 4983230072969 + 3 ^ 40 * 8375250 * 2
def baseEnd_8375250 : Nat := 4300528851568462029557933

theorem tailTrace_8375250 : CollatzResearch.WordTrace tailWord_8375250 prefixEnd_8375250 4300528851568462029557933 := by
  unfold tailWord_8375250
  simp only [CollatzResearch.WordTrace]
  refine ⟨76367615726976775916708801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203646975271938069111223469 76367615726976775916708801)
  ·
    refine ⟨57275711795232581937531601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76367615726976775916708801 57275711795232581937531601)
    ·
      refine ⟨42956783846424436453148701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57275711795232581937531601 42956783846424436453148701)
      ·
        refine ⟨16108793942409163669930763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42956783846424436453148701 16108793942409163669930763)
        ·
          refine ⟨24163190913613745504896145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16108793942409163669930763 24163190913613745504896145)
          ·
            refine ⟨18122393185210309128672109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24163190913613745504896145 18122393185210309128672109)
            ·
              refine ⟨6795897444453865923252041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18122393185210309128672109 6795897444453865923252041)
              ·
                refine ⟨5096923083340399442439031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795897444453865923252041 5096923083340399442439031)
                ·
                  refine ⟨7645384625010599163658547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096923083340399442439031 7645384625010599163658547)
                  ·
                    refine ⟨11468076937515898745487821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7645384625010599163658547 11468076937515898745487821)
                    ·
                      refine ⟨4300528851568462029557933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468076937515898745487821 4300528851568462029557933)
                      ·
                        rfl

theorem cell23_8375250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_8375250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375250 prefixEnd_8375250 := by exact prefixLift 8375250
  have htrace : WordTrace (prefixWord ++ tailWord_8375250) baseStart_8375250 baseEnd_8375250 := by
    simpa [prefixWord, tailWord_8375250, baseEnd_8375250] using wordTrace_append hprefix tailTrace_8375250
  have hstable : (prefixWord ++ tailWord_8375250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375250).length < 2 ^ (prefixWord ++ tailWord_8375250).sum := by decide
  have hdescent : baseEnd_8375250 < baseStart_8375250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375252 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_8375252 : Nat := 118140960795 + 8375252 * 2 ^ 59
def prefixEnd_8375252 : Nat := 4983230072969 + 3 ^ 40 * 8375252 * 2
def baseEnd_8375252 : Nat := 4300529878529771021732923

theorem tailTrace_8375252 : CollatzResearch.WordTrace tailWord_8375252 prefixEnd_8375252 4300529878529771021732923 := by
  unfold tailWord_8375252
  simp only [CollatzResearch.WordTrace]
  refine ⟨152735267926949929004204005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203647023902599905338938673 152735267926949929004204005)
  ·
    refine ⟨28637862736303111688288251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152735267926949929004204005 28637862736303111688288251)
    ·
      refine ⟨42956794104454667532432377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28637862736303111688288251 42956794104454667532432377)
      ·
        refine ⟨32217595578341000649324283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42956794104454667532432377 32217595578341000649324283)
        ·
          refine ⟨48326393367511500973986425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32217595578341000649324283 48326393367511500973986425)
          ·
            refine ⟨36244795025633625730489819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48326393367511500973986425 36244795025633625730489819)
            ·
              refine ⟨54367192538450438595734729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36244795025633625730489819 54367192538450438595734729)
              ·
                refine ⟨40775394403837828946801047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54367192538450438595734729 40775394403837828946801047)
                ·
                  refine ⟨61163091605756743420201571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40775394403837828946801047 61163091605756743420201571)
                  ·
                    refine ⟨91744637408635115130302357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61163091605756743420201571 91744637408635115130302357)
                    ·
                      refine ⟨4300529878529771021732923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91744637408635115130302357 4300529878529771021732923)
                      ·
                        rfl

theorem cell23_8375252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_8375252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375252 prefixEnd_8375252 := by exact prefixLift 8375252
  have htrace : WordTrace (prefixWord ++ tailWord_8375252) baseStart_8375252 baseEnd_8375252 := by
    simpa [prefixWord, tailWord_8375252, baseEnd_8375252] using wordTrace_append hprefix tailTrace_8375252
  have hstable : (prefixWord ++ tailWord_8375252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375252).length < 2 ^ (prefixWord ++ tailWord_8375252).sum := by decide
  have hdescent : baseEnd_8375252 < baseStart_8375252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375256 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_8375256 : Nat := 118140960795 + 8375256 * 2 ^ 59
def prefixEnd_8375256 : Nat := 4983230072969 + 3 ^ 40 * 8375256 * 2
def baseEnd_8375256 : Nat := 4300531932452389006082905

theorem tailTrace_8375256 : CollatzResearch.WordTrace tailWord_8375256 prefixEnd_8375256 4300531932452389006082905 := by
  unfold tailWord_8375256
  simp only [CollatzResearch.WordTrace]
  refine ⟨152735340872942683345776811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203647121163923577794369081 152735340872942683345776811)
  ·
    refine ⟨229103011309414025018665217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152735340872942683345776811 229103011309414025018665217)
    ·
      refine ⟨171827258482060518763998913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229103011309414025018665217 171827258482060518763998913)
      ·
        refine ⟨128870443861545389072999185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171827258482060518763998913 128870443861545389072999185)
        ·
          refine ⟨96652832896159041804749389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128870443861545389072999185 96652832896159041804749389)
          ·
            refine ⟨36244812336059640676781021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96652832896159041804749389 36244812336059640676781021)
            ·
              refine ⟨13591804626022365253792883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36244812336059640676781021 13591804626022365253792883)
              ·
                refine ⟨20387706939033547880689325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591804626022365253792883 20387706939033547880689325)
                ·
                  refine ⟨7645390102137580455258497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20387706939033547880689325 7645390102137580455258497)
                  ·
                    refine ⟨5734042576603185341443873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645390102137580455258497 5734042576603185341443873)
                    ·
                      refine ⟨4300531932452389006082905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734042576603185341443873 4300531932452389006082905)
                      ·
                        rfl

theorem cell23_8375256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_8375256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375256 prefixEnd_8375256 := by exact prefixLift 8375256
  have htrace : WordTrace (prefixWord ++ tailWord_8375256) baseStart_8375256 baseEnd_8375256 := by
    simpa [prefixWord, tailWord_8375256, baseEnd_8375256] using wordTrace_append hprefix tailTrace_8375256
  have hstable : (prefixWord ++ tailWord_8375256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375256).length < 2 ^ (prefixWord ++ tailWord_8375256).sum := by decide
  have hdescent : baseEnd_8375256 < baseStart_8375256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375265 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_8375265 : Nat := 118140960795 + 8375265 * 2 ^ 59
def prefixEnd_8375265 : Nat := 4983230072969 + 3 ^ 40 * 8375265 * 2
def baseEnd_8375265 : Nat := 4300536553778279470870363

theorem tailTrace_8375265 : CollatzResearch.WordTrace tailWord_8375265 prefixEnd_8375265 4300536553778279470870363 := by
  unfold tailWord_8375265
  simp only [CollatzResearch.WordTrace]
  refine ⟨305471010002852761228631249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203647340001901840819087499 305471010002852761228631249)
  ·
    refine ⟨229103257502139570921473437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305471010002852761228631249 229103257502139570921473437)
    ·
      refine ⟨85913721563302339095552539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229103257502139570921473437 85913721563302339095552539)
      ·
        refine ⟨128870582344953508643328809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85913721563302339095552539 128870582344953508643328809)
        ·
          refine ⟨96652936758715131482496607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128870582344953508643328809 96652936758715131482496607)
          ·
            refine ⟨144979405138072697223744911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96652936758715131482496607 144979405138072697223744911)
            ·
              refine ⟨217469107707109045835617367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144979405138072697223744911 217469107707109045835617367)
              ·
                refine ⟨326203661560663568753426051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217469107707109045835617367 326203661560663568753426051)
                ·
                  refine ⟨489305492340995353130139077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326203661560663568753426051 489305492340995353130139077)
                  ·
                    refine ⟨91744779813936628711901077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489305492340995353130139077 91744779813936628711901077)
                    ·
                      refine ⟨4300536553778279470870363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91744779813936628711901077 4300536553778279470870363)
                      ·
                        rfl

theorem cell23_8375265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_8375265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375265 prefixEnd_8375265 := by exact prefixLift 8375265
  have htrace : WordTrace (prefixWord ++ tailWord_8375265) baseStart_8375265 baseEnd_8375265 := by
    simpa [prefixWord, tailWord_8375265, baseEnd_8375265] using wordTrace_append hprefix tailTrace_8375265
  have hstable : (prefixWord ++ tailWord_8375265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375265).length < 2 ^ (prefixWord ++ tailWord_8375265).sum := by decide
  have hdescent : baseEnd_8375265 < baseStart_8375265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375305 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_8375305 : Nat := 118140960795 + 8375305 * 2 ^ 59
def prefixEnd_8375305 : Nat := 4983230072969 + 3 ^ 40 * 8375305 * 2
def baseEnd_8375305 : Nat := 1433519031001486438123393

theorem tailTrace_8375305 : CollatzResearch.WordTrace tailWord_8375305 prefixEnd_8375305 1433519031001486438123393 := by
  unfold tailWord_8375305
  simp only [CollatzResearch.WordTrace]
  refine ⟨305472468922707848060087369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203648312615138565373391579 305472468922707848060087369)
  ·
    refine ⟨229104351692030886045065527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305472468922707848060087369 229104351692030886045065527)
    ·
      refine ⟨343656527538046329067598291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229104351692030886045065527 343656527538046329067598291)
      ·
        refine ⟨515484791307069493601397437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343656527538046329067598291 515484791307069493601397437)
        ·
          refine ⟨193306796740151060100524039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515484791307069493601397437 193306796740151060100524039)
          ·
            refine ⟨289960195110226590150786059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193306796740151060100524039 289960195110226590150786059)
            ·
              refine ⟨434940292665339885226179089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289960195110226590150786059 434940292665339885226179089)
              ·
                refine ⟨326205219499004913919634317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434940292665339885226179089 326205219499004913919634317)
                ·
                  refine ⟨122326957312126842719862869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326205219499004913919634317 122326957312126842719862869)
                  ·
                    refine ⟨1433519031001486438123393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122326957312126842719862869 1433519031001486438123393)
                    ·
                      rfl

theorem cell23_8375305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_8375305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375305 prefixEnd_8375305 := by exact prefixLift 8375305
  have htrace : WordTrace (prefixWord ++ tailWord_8375305) baseStart_8375305 baseEnd_8375305 := by
    simpa [prefixWord, tailWord_8375305, baseEnd_8375305] using wordTrace_append hprefix tailTrace_8375305
  have hstable : (prefixWord ++ tailWord_8375305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375305).length < 2 ^ (prefixWord ++ tailWord_8375305).sum := by decide
  have hdescent : baseEnd_8375305 < baseStart_8375305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375306 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_8375306 : Nat := 118140960795 + 8375306 * 2 ^ 59
def prefixEnd_8375306 : Nat := 4983230072969 + 3 ^ 40 * 8375306 * 2
def baseEnd_8375306 : Nat := 4300557606485113810457675

theorem tailTrace_8375306 : CollatzResearch.WordTrace tailWord_8375306 prefixEnd_8375306 4300557606485113810457675 := by
  unfold tailWord_8375306
  simp only [CollatzResearch.WordTrace]
  refine ⟨76368126348926056307718443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203648336930469483487249181 76368126348926056307718443)
  ·
    refine ⟨114552189523389084461577665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76368126348926056307718443 114552189523389084461577665)
    ·
      refine ⟨85914142142541813346183249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114552189523389084461577665 85914142142541813346183249)
      ·
        refine ⟨64435606606906360009637437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85914142142541813346183249 64435606606906360009637437)
        ·
          refine ⟨24163352477589885003614039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64435606606906360009637437 24163352477589885003614039)
          ·
            refine ⟨36245028716384827505421059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24163352477589885003614039 36245028716384827505421059)
            ·
              refine ⟨54367543074577241258131589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36245028716384827505421059 54367543074577241258131589)
              ·
                refine ⟨10193914326483232735899673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54367543074577241258131589 10193914326483232735899673)
                ·
                  refine ⟨7645435744862424551924755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10193914326483232735899673 7645435744862424551924755)
                  ·
                    refine ⟨11468153617293636827887133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7645435744862424551924755 11468153617293636827887133)
                    ·
                      refine ⟨4300557606485113810457675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468153617293636827887133 4300557606485113810457675)
                      ·
                        rfl

theorem cell23_8375306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_8375306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375306 prefixEnd_8375306 := by exact prefixLift 8375306
  have htrace : WordTrace (prefixWord ++ tailWord_8375306) baseStart_8375306 baseEnd_8375306 := by
    simpa [prefixWord, tailWord_8375306, baseEnd_8375306] using wordTrace_append hprefix tailTrace_8375306
  have hstable : (prefixWord ++ tailWord_8375306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375306).length < 2 ^ (prefixWord ++ tailWord_8375306).sum := by decide
  have hdescent : baseEnd_8375306 < baseStart_8375306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375322 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_8375322 : Nat := 118140960795 + 8375322 * 2 ^ 59
def prefixEnd_8375322 : Nat := 4983230072969 + 3 ^ 40 * 8375322 * 2
def baseEnd_8375322 : Nat := 1433521940725195249285867

theorem tailTrace_8375322 : CollatzResearch.WordTrace tailWord_8375322 prefixEnd_8375322 1433521940725195249285867 := by
  unfold tailWord_8375322
  simp only [CollatzResearch.WordTrace]
  refine ⟨76368272240911564990864055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203648725975764173308970813 76368272240911564990864055)
  ·
    refine ⟨114552408361367347486296083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76368272240911564990864055 114552408361367347486296083)
    ·
      refine ⟨171828612542051021229444125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114552408361367347486296083 171828612542051021229444125)
      ·
        refine ⟨64435729703269132961041547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171828612542051021229444125 64435729703269132961041547)
        ·
          refine ⟨96653594554903699441562321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64435729703269132961041547 96653594554903699441562321)
          ·
            refine ⟨72490195916177774581171741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96653594554903699441562321 72490195916177774581171741)
            ·
              refine ⟨27183823468566665467939403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72490195916177774581171741 27183823468566665467939403)
              ·
                refine ⟨40775735202849998201909105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27183823468566665467939403 40775735202849998201909105)
                ·
                  refine ⟨30581801402137498651431829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40775735202849998201909105 30581801402137498651431829)
                  ·
                    refine ⟨1433521940725195249285867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30581801402137498651431829 1433521940725195249285867)
                    ·
                      rfl

theorem cell23_8375322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_8375322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375322 prefixEnd_8375322 := by exact prefixLift 8375322
  have htrace : WordTrace (prefixWord ++ tailWord_8375322) baseStart_8375322 baseEnd_8375322 := by
    simpa [prefixWord, tailWord_8375322, baseEnd_8375322] using wordTrace_append hprefix tailTrace_8375322
  have hstable : (prefixWord ++ tailWord_8375322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375322).length < 2 ^ (prefixWord ++ tailWord_8375322).sum := by decide
  have hdescent : baseEnd_8375322 < baseStart_8375322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375346 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_8375346 : Nat := 118140960795 + 8375346 * 2 ^ 59
def prefixEnd_8375346 : Nat := 4983230072969 + 3 ^ 40 * 8375346 * 2
def baseEnd_8375346 : Nat := 4300578145711293653957491

theorem tailTrace_8375346 : CollatzResearch.WordTrace tailWord_8375346 prefixEnd_8375346 4300578145711293653957491 := by
  unfold tailWord_8375346
  simp only [CollatzResearch.WordTrace]
  refine ⟨76368491078889828015582473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203649309543706208041553261 76368491078889828015582473)
  ·
    refine ⟨57276368309167371011686855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76368491078889828015582473 57276368309167371011686855)
    ·
      refine ⟨85914552463751056517530283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57276368309167371011686855 85914552463751056517530283)
      ·
        refine ⟨128871828695626584776295425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85914552463751056517530283 128871828695626584776295425)
        ·
          refine ⟨96653871521719938582221569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128871828695626584776295425 96653871521719938582221569)
          ·
            refine ⟨72490403641289953936666177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96653871521719938582221569 72490403641289953936666177)
            ·
              refine ⟨54367802730967465452499633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72490403641289953936666177 54367802730967465452499633)
              ·
                refine ⟨40775852048225599089374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54367802730967465452499633 40775852048225599089374725)
                ·
                  refine ⟨7645472259042299829257761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40775852048225599089374725 7645472259042299829257761)
                  ·
                    refine ⟨5734104194281724871943321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645472259042299829257761 5734104194281724871943321)
                    ·
                      refine ⟨4300578145711293653957491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734104194281724871943321 4300578145711293653957491)
                      ·
                        rfl

theorem cell23_8375346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_8375346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375346 prefixEnd_8375346 := by exact prefixLift 8375346
  have htrace : WordTrace (prefixWord ++ tailWord_8375346) baseStart_8375346 baseEnd_8375346 := by
    simpa [prefixWord, tailWord_8375346, baseEnd_8375346] using wordTrace_append hprefix tailTrace_8375346
  have hstable : (prefixWord ++ tailWord_8375346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375346).length < 2 ^ (prefixWord ++ tailWord_8375346).sum := by decide
  have hdescent : baseEnd_8375346 < baseStart_8375346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375350 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_8375350 : Nat := 118140960795 + 8375350 * 2 ^ 59
def prefixEnd_8375350 : Nat := 4983230072969 + 3 ^ 40 * 8375350 * 2
def baseEnd_8375350 : Nat := 4300580199633911638307473

theorem tailTrace_8375350 : CollatzResearch.WordTrace tailWord_8375350 prefixEnd_8375350 4300580199633911638307473 := by
  unfold tailWord_8375350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092131887971551296592219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203649406805029880496983669 19092131887971551296592219)
  ·
    refine ⟨28638197831957326944888329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092131887971551296592219 28638197831957326944888329)
    ·
      refine ⟨21478648373967995208666247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28638197831957326944888329 21478648373967995208666247)
      ·
        refine ⟨32217972560951992812999371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21478648373967995208666247 32217972560951992812999371)
        ·
          refine ⟨48326958841427989219499057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32217972560951992812999371 48326958841427989219499057)
          ·
            refine ⟨36245219131070991914624293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48326958841427989219499057 36245219131070991914624293)
            ·
              refine ⟨6795978587075810983992055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36245219131070991914624293 6795978587075810983992055)
              ·
                refine ⟨10193967880613716475988083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795978587075810983992055 10193967880613716475988083)
                ·
                  refine ⟨15290951820920574713982125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193967880613716475988083 15290951820920574713982125)
                  ·
                    refine ⟨5734106932845215517743297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15290951820920574713982125 5734106932845215517743297)
                    ·
                      refine ⟨4300580199633911638307473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734106932845215517743297 4300580199633911638307473)
                      ·
                        rfl

theorem cell23_8375350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_8375350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375350 prefixEnd_8375350 := by exact prefixLift 8375350
  have htrace : WordTrace (prefixWord ++ tailWord_8375350) baseStart_8375350 baseEnd_8375350 := by
    simpa [prefixWord, tailWord_8375350, baseEnd_8375350] using wordTrace_append hprefix tailTrace_8375350
  have hstable : (prefixWord ++ tailWord_8375350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375350).length < 2 ^ (prefixWord ++ tailWord_8375350).sum := by decide
  have hdescent : baseEnd_8375350 < baseStart_8375350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375419 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 4, 4, 2]
def baseStart_8375419 : Nat := 118140960795 + 8375419 * 2 ^ 59
def prefixEnd_8375419 : Nat := 4983230072969 + 3 ^ 40 * 8375419 * 2
def baseEnd_8375419 : Nat := 4300615629799071868344655

theorem tailTrace_8375419 : CollatzResearch.WordTrace tailWord_8375419 prefixEnd_8375419 4300615629799071868344655 := by
  unfold tailWord_8375419
  simp only [CollatzResearch.WordTrace]
  refine ⟨305476626844294845529737311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203651084562863230353158207 305476626844294845529737311)
  ·
    refine ⟨458214940266442268294605967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305476626844294845529737311 458214940266442268294605967)
    ·
      refine ⟨687322410399663402441908951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458214940266442268294605967 687322410399663402441908951)
      ·
        refine ⟨1030983615599495103662863427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687322410399663402441908951 1030983615599495103662863427)
        ·
          refine ⟨1546475423399242655494295141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030983615599495103662863427 1546475423399242655494295141)
          ·
            refine ⟨289964141887357997905180339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1546475423399242655494295141 289964141887357997905180339)
            ·
              refine ⟨434946212831036996857770509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289964141887357997905180339 434946212831036996857770509)
              ·
                refine ⟨163104829811638873821663941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434946212831036996857770509 163104829811638873821663941)
                ·
                  refine ⟨30582155589682288841561989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163104829811638873821663941 30582155589682288841561989)
                  ·
                    refine ⟨5734154173065429157792873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30582155589682288841561989 5734154173065429157792873)
                    ·
                      refine ⟨4300615629799071868344655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734154173065429157792873 4300615629799071868344655)
                      ·
                        rfl

theorem cell23_8375419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4, 2].length) (baseStart_8375419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375419 prefixEnd_8375419 := by exact prefixLift 8375419
  have htrace : WordTrace (prefixWord ++ tailWord_8375419) baseStart_8375419 baseEnd_8375419 := by
    simpa [prefixWord, tailWord_8375419, baseEnd_8375419] using wordTrace_append hprefix tailTrace_8375419
  have hstable : (prefixWord ++ tailWord_8375419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375419).length < 2 ^ (prefixWord ++ tailWord_8375419).sum := by decide
  have hdescent : baseEnd_8375419 < baseStart_8375419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375456 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_8375456 : Nat := 118140960795 + 8375456 * 2 ^ 59
def prefixEnd_8375456 : Nat := 4983230072969 + 3 ^ 40 * 8375456 * 2
def baseEnd_8375456 : Nat := 4300634628583288223581985

theorem tailTrace_8375456 : CollatzResearch.WordTrace tailWord_8375456 prefixEnd_8375456 4300634628583288223581985 := by
  unfold tailWord_8375456
  simp only [CollatzResearch.WordTrace]
  refine ⟨152738988172580400424417111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203651984230107200565889481 152738988172580400424417111)
  ·
    refine ⟨229108482258870600636625667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152738988172580400424417111 229108482258870600636625667)
    ·
      refine ⟨343662723388305900954938501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229108482258870600636625667 343662723388305900954938501)
      ·
        refine ⟨64436760635307356429050969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343662723388305900954938501 64436760635307356429050969)
        ·
          refine ⟨48327570476480517321788227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64436760635307356429050969 48327570476480517321788227)
          ·
            refine ⟨72491355714720775982682341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48327570476480517321788227 72491355714720775982682341)
            ·
              refine ⟨13592129196510145496752939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72491355714720775982682341 13592129196510145496752939)
              ·
                refine ⟨20388193794765218245129409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13592129196510145496752939 20388193794765218245129409)
                ·
                  refine ⟨15291145346073913683847057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20388193794765218245129409 15291145346073913683847057)
                  ·
                    refine ⟨11468359009555435262885293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15291145346073913683847057 11468359009555435262885293)
                    ·
                      refine ⟨4300634628583288223581985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468359009555435262885293 4300634628583288223581985)
                      ·
                        rfl

theorem cell23_8375456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_8375456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375456 prefixEnd_8375456 := by exact prefixLift 8375456
  have htrace : WordTrace (prefixWord ++ tailWord_8375456) baseStart_8375456 baseEnd_8375456 := by
    simpa [prefixWord, tailWord_8375456, baseEnd_8375456] using wordTrace_append hprefix tailTrace_8375456
  have hstable : (prefixWord ++ tailWord_8375456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375456).length < 2 ^ (prefixWord ++ tailWord_8375456).sum := by decide
  have hdescent : baseEnd_8375456 < baseStart_8375456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375496 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_8375496 : Nat := 118140960795 + 8375496 * 2 ^ 59
def prefixEnd_8375496 : Nat := 4983230072969 + 3 ^ 40 * 8375496 * 2
def baseEnd_8375496 : Nat := 4300655167809468067081801

theorem tailTrace_8375496 : CollatzResearch.WordTrace tailWord_8375496 prefixEnd_8375496 4300655167809468067081801 := by
  unfold tailWord_8375496
  simp only [CollatzResearch.WordTrace]
  refine ⟨152739717632507943840145171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203652956843343925120193561 152739717632507943840145171)
  ·
    refine ⟨229109576448761915760217757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152739717632507943840145171 229109576448761915760217757)
    ·
      refine ⟨85916091168285718410081659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229109576448761915760217757 85916091168285718410081659)
      ·
        refine ⟨128874136752428577615122489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85916091168285718410081659 128874136752428577615122489)
        ·
          refine ⟨96655602564321433211341867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128874136752428577615122489 96655602564321433211341867)
          ·
            refine ⟨144983403846482149817012801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96655602564321433211341867 144983403846482149817012801)
            ·
              refine ⟨108737552884861612362759601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144983403846482149817012801 108737552884861612362759601)
              ·
                refine ⟨81553164663646209272069701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108737552884861612362759601 81553164663646209272069701)
                ·
                  refine ⟨15291218374433664238513069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81553164663646209272069701 15291218374433664238513069)
                  ·
                    refine ⟨5734206890412624089442401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15291218374433664238513069 5734206890412624089442401)
                    ·
                      refine ⟨4300655167809468067081801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734206890412624089442401 4300655167809468067081801)
                      ·
                        rfl

theorem cell23_8375496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_8375496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375496 prefixEnd_8375496 := by exact prefixLift 8375496
  have htrace : WordTrace (prefixWord ++ tailWord_8375496) baseStart_8375496 baseEnd_8375496 := by
    simpa [prefixWord, tailWord_8375496, baseEnd_8375496] using wordTrace_append hprefix tailTrace_8375496
  have hstable : (prefixWord ++ tailWord_8375496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375496).length < 2 ^ (prefixWord ++ tailWord_8375496).sum := by decide
  have hdescent : baseEnd_8375496 < baseStart_8375496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375506 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_8375506 : Nat := 118140960795 + 8375506 * 2 ^ 59
def prefixEnd_8375506 : Nat := 4983230072969 + 3 ^ 40 * 8375506 * 2
def baseEnd_8375506 : Nat := 1433553434205337675985585

theorem tailTrace_8375506 : CollatzResearch.WordTrace tailWord_8375506 prefixEnd_8375506 1433553434205337675985585 := by
  unfold tailWord_8375506
  simp only [CollatzResearch.WordTrace]
  refine ⟨76369949998744914847038593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203653199996653106258769581 76369949998744914847038593)
  ·
    refine ⟨57277462499058686135278945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76369949998744914847038593 57277462499058686135278945)
    ·
      refine ⟨42958096874294014601459209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57277462499058686135278945 42958096874294014601459209)
      ·
        refine ⟨32218572655720510951094407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42958096874294014601459209 32218572655720510951094407)
        ·
          refine ⟨48327858983580766426641611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32218572655720510951094407 48327858983580766426641611)
          ·
            refine ⟨72491788475371149639962417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48327858983580766426641611 72491788475371149639962417)
            ·
              refine ⟨54368841356528362229971813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72491788475371149639962417 54368841356528362229971813)
              ·
                refine ⟨10194157754349067918119715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54368841356528362229971813 10194157754349067918119715)
                ·
                  refine ⟨15291236631523601877179573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194157754349067918119715 15291236631523601877179573)
                  ·
                    refine ⟨1433553434205337675985585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15291236631523601877179573 1433553434205337675985585)
                    ·
                      rfl

theorem cell23_8375506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_8375506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375506 prefixEnd_8375506 := by exact prefixLift 8375506
  have htrace : WordTrace (prefixWord ++ tailWord_8375506) baseStart_8375506 baseEnd_8375506 := by
    simpa [prefixWord, tailWord_8375506, baseEnd_8375506] using wordTrace_append hprefix tailTrace_8375506
  have hstable : (prefixWord ++ tailWord_8375506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375506).length < 2 ^ (prefixWord ++ tailWord_8375506).sum := by decide
  have hdescent : baseEnd_8375506 < baseStart_8375506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375519 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 1, 6]
def baseStart_8375519 : Nat := 118140960795 + 8375519 * 2 ^ 59
def prefixEnd_8375519 : Nat := 4983230072969 + 3 ^ 40 * 8375519 * 2
def baseEnd_8375519 : Nat := 1433555659288173825698065

theorem tailTrace_8375519 : CollatzResearch.WordTrace tailWord_8375519 prefixEnd_8375519 1433555659288173825698065 := by
  unfold tailWord_8375519
  simp only [CollatzResearch.WordTrace]
  refine ⟨305480274143932562608377611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203653516095955041738918407 305480274143932562608377611)
  ·
    refine ⟨458220411215898843912566417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305480274143932562608377611 458220411215898843912566417)
    ·
      refine ⟨343665308411924132934424813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458220411215898843912566417 343665308411924132934424813)
      ·
        refine ⟨128874490654471549850409305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343665308411924132934424813 128874490654471549850409305)
        ·
          refine ⟨96655867990853662387806979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128874490654471549850409305 96655867990853662387806979)
          ·
            refine ⟨144983801986280493581710469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96655867990853662387806979 144983801986280493581710469)
            ·
              refine ⟨27184462872427592546570713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144983801986280493581710469 27184462872427592546570713)
              ·
                refine ⟨20388347154320694409928035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27184462872427592546570713 20388347154320694409928035)
                ·
                  refine ⟨30582520731481041614892053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20388347154320694409928035 30582520731481041614892053)
                  ·
                    refine ⟨1433555659288173825698065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30582520731481041614892053 1433555659288173825698065)
                    ·
                      rfl

theorem cell23_8375519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_8375519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375519 prefixEnd_8375519 := by exact prefixLift 8375519
  have htrace : WordTrace (prefixWord ++ tailWord_8375519) baseStart_8375519 baseEnd_8375519 := by
    simpa [prefixWord, tailWord_8375519, baseEnd_8375519] using wordTrace_append hprefix tailTrace_8375519
  have hstable : (prefixWord ++ tailWord_8375519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375519).length < 2 ^ (prefixWord ++ tailWord_8375519).sum := by decide
  have hdescent : baseEnd_8375519 < baseStart_8375519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375520 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 1, 1, 3]
def baseStart_8375520 : Nat := 118140960795 + 8375520 * 2 ^ 59
def prefixEnd_8375520 : Nat := 4983230072969 + 3 ^ 40 * 8375520 * 2
def baseEnd_8375520 : Nat := 4300667491345175973181691

theorem tailTrace_8375520 : CollatzResearch.WordTrace tailWord_8375520 prefixEnd_8375520 4300667491345175973181691 := by
  unfold tailWord_8375520
  simp only [CollatzResearch.WordTrace]
  refine ⟨152740155308464469889582007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203653540411285959852776009 152740155308464469889582007)
  ·
    refine ⟨229110232962696704834373011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152740155308464469889582007 229110232962696704834373011)
    ·
      refine ⟨343665349444045057251559517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229110232962696704834373011 343665349444045057251559517)
      ·
        refine ⟨128874506041516896469334819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343665349444045057251559517 128874506041516896469334819)
        ·
          refine ⟨193311759062275344704002229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128874506041516896469334819 193311759062275344704002229)
          ·
            refine ⟨18122977412088313566000209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193311759062275344704002229 18122977412088313566000209)
            ·
              refine ⟨13592233059066235174500157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18122977412088313566000209 13592233059066235174500157)
              ·
                refine ⟨5097087397149838190437559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13592233059066235174500157 5097087397149838190437559)
                ·
                  refine ⟨7645631095724757285656339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097087397149838190437559 7645631095724757285656339)
                  ·
                    refine ⟨11468446643587135928484509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7645631095724757285656339 11468446643587135928484509)
                    ·
                      refine ⟨4300667491345175973181691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468446643587135928484509 4300667491345175973181691)
                      ·
                        rfl

theorem cell23_8375520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_8375520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375520 prefixEnd_8375520 := by exact prefixLift 8375520
  have htrace : WordTrace (prefixWord ++ tailWord_8375520) baseStart_8375520 baseEnd_8375520 := by
    simpa [prefixWord, tailWord_8375520, baseEnd_8375520] using wordTrace_append hprefix tailTrace_8375520
  have hstable : (prefixWord ++ tailWord_8375520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375520).length < 2 ^ (prefixWord ++ tailWord_8375520).sum := by decide
  have hdescent : baseEnd_8375520 < baseStart_8375520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375556 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_8375556 : Nat := 118140960795 + 8375556 * 2 ^ 59
def prefixEnd_8375556 : Nat := 4983230072969 + 3 ^ 40 * 8375556 * 2
def baseEnd_8375556 : Nat := 4300685976648737832331525

theorem tailTrace_8375556 : CollatzResearch.WordTrace tailWord_8375556 prefixEnd_8375556 4300685976648737832331525 := by
  unfold tailWord_8375556
  simp only [CollatzResearch.WordTrace]
  refine ⟨152740811822399258963737261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203654415763199011951649681 152740811822399258963737261)
  ·
    refine ⟨57277804433399722111401473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152740811822399258963737261 57277804433399722111401473)
    ·
      refine ⟨42958353325049791583551105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57277804433399722111401473 42958353325049791583551105)
      ·
        refine ⟨32218764993787343687663329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42958353325049791583551105 32218764993787343687663329)
        ·
          refine ⟨24164073745340507765747497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32218764993787343687663329 24164073745340507765747497)
          ·
            refine ⟨18123055309005380824310623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24164073745340507765747497 18123055309005380824310623)
            ·
              refine ⟨27184582963508071236465935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18123055309005380824310623 27184582963508071236465935)
              ·
                refine ⟨40776874445262106854698903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27184582963508071236465935 40776874445262106854698903)
                ·
                  refine ⟨61165311667893160282048355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40776874445262106854698903 61165311667893160282048355)
                  ·
                    refine ⟨91747967501839740423072533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61165311667893160282048355 91747967501839740423072533)
                    ·
                      refine ⟨4300685976648737832331525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91747967501839740423072533 4300685976648737832331525)
                      ·
                        rfl

theorem cell23_8375556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_8375556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375556 prefixEnd_8375556 := by exact prefixLift 8375556
  have htrace : WordTrace (prefixWord ++ tailWord_8375556) baseStart_8375556 baseEnd_8375556 := by
    simpa [prefixWord, tailWord_8375556, baseEnd_8375556] using wordTrace_append hprefix tailTrace_8375556
  have hstable : (prefixWord ++ tailWord_8375556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375556).length < 2 ^ (prefixWord ++ tailWord_8375556).sum := by decide
  have hdescent : baseEnd_8375556 < baseStart_8375556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375563 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 3]
def baseStart_8375563 : Nat := 118140960795 + 8375563 * 2 ^ 59
def prefixEnd_8375563 : Nat := 4983230072969 + 3 ^ 40 * 8375563 * 2
def baseEnd_8375563 : Nat := 4300689571013319304943993

theorem tailTrace_8375563 : CollatzResearch.WordTrace tailWord_8375563 prefixEnd_8375563 4300689571013319304943993 := by
  unfold tailWord_8375563
  simp only [CollatzResearch.WordTrace]
  refine ⟨305481878955773158122979343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203654585970515438748652895 305481878955773158122979343)
  ·
    refine ⟨458222818433659737184469015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305481878955773158122979343 458222818433659737184469015)
    ·
      refine ⟨687334227650489605776703523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458222818433659737184469015 687334227650489605776703523)
      ·
        refine ⟨1031001341475734408665055285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687334227650489605776703523 1031001341475734408665055285)
        ·
          refine ⟨96656375763350100812348933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1031001341475734408665055285 96656375763350100812348933)
          ·
            refine ⟨18123070455628143902315425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96656375763350100812348933 18123070455628143902315425)
            ·
              refine ⟨13592302841721107926736569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18123070455628143902315425 13592302841721107926736569)
              ·
                refine ⟨10194227131290830945052427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13592302841721107926736569 10194227131290830945052427)
                ·
                  refine ⟨15291340696936246417578641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194227131290830945052427 15291340696936246417578641)
                  ·
                    refine ⟨11468505522702184813183981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15291340696936246417578641 11468505522702184813183981)
                    ·
                      refine ⟨4300689571013319304943993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468505522702184813183981 4300689571013319304943993)
                      ·
                        rfl

theorem cell23_8375563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 2, 3].length) (baseStart_8375563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375563 prefixEnd_8375563 := by exact prefixLift 8375563
  have htrace : WordTrace (prefixWord ++ tailWord_8375563) baseStart_8375563 baseEnd_8375563 := by
    simpa [prefixWord, tailWord_8375563, baseEnd_8375563] using wordTrace_append hprefix tailTrace_8375563
  have hstable : (prefixWord ++ tailWord_8375563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375563).length < 2 ^ (prefixWord ++ tailWord_8375563).sum := by decide
  have hdescent : baseEnd_8375563 < baseStart_8375563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375566 : List Nat := [4, 1, 1, 2, 1, 3, 4, 7]
def baseStart_8375566 : Nat := 118140960795 + 8375566 * 2 ^ 59
def prefixEnd_8375566 : Nat := 4983230072969 + 3 ^ 40 * 8375566 * 2
def baseEnd_8375566 : Nat := 159284855979825288637277

theorem tailTrace_8375566 : CollatzResearch.WordTrace tailWord_8375566 prefixEnd_8375566 159284855979825288637277 := by
  unfold tailWord_8375566
  simp only [CollatzResearch.WordTrace]
  refine ⟨38185248546845286204417319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203654658916508193090225701 38185248546845286204417319)
  ·
    refine ⟨57277872820267929306625979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38185248546845286204417319 57277872820267929306625979)
    ·
      refine ⟨85916809230401893959938969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57277872820267929306625979 85916809230401893959938969)
      ·
        refine ⟨64437606922801420469954227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85916809230401893959938969 64437606922801420469954227)
        ·
          refine ⟨96656410384202130704931341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64437606922801420469954227 96656410384202130704931341)
          ·
            refine ⟨36246153894075799014349253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96656410384202130704931341 36246153894075799014349253)
            ·
              refine ⟨6796153855139212315190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36246153894075799014349253 6796153855139212315190485)
              ·
                refine ⟨159284855979825288637277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6796153855139212315190485 159284855979825288637277)
                ·
                  rfl

theorem cell23_8375566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_8375566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375566 prefixEnd_8375566 := by exact prefixLift 8375566
  have htrace : WordTrace (prefixWord ++ tailWord_8375566) baseStart_8375566 baseEnd_8375566 := by
    simpa [prefixWord, tailWord_8375566, baseEnd_8375566] using wordTrace_append hprefix tailTrace_8375566
  have hstable : (prefixWord ++ tailWord_8375566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375566).length < 2 ^ (prefixWord ++ tailWord_8375566).sum := by decide
  have hdescent : baseEnd_8375566 < baseStart_8375566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375599 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_8375599 : Nat := 118140960795 + 8375599 * 2 ^ 59
def prefixEnd_8375599 : Nat := 4983230072969 + 3 ^ 40 * 8375599 * 2
def baseEnd_8375599 : Nat := 4300708056316881164093827

theorem tailTrace_8375599 : CollatzResearch.WordTrace tailWord_8375599 prefixEnd_8375599 4300708056316881164093827 := by
  unfold tailWord_8375599
  simp only [CollatzResearch.WordTrace]
  refine ⟨305483191983642736271289851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203655461322428490847526567 305483191983642736271289851)
  ·
    refine ⟨458224787975464104406934777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305483191983642736271289851 458224787975464104406934777)
    ·
      refine ⟨343668590981598078305201083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458224787975464104406934777 343668590981598078305201083)
      ·
        refine ⟨515502886472397117457801625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343668590981598078305201083 515502886472397117457801625)
        ·
          refine ⟨386627164854297838093351219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515502886472397117457801625 386627164854297838093351219)
          ·
            refine ⟨579940747281446757140026829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386627164854297838093351219 579940747281446757140026829)
            ·
              refine ⟨217477780230542533927510061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579940747281446757140026829 217477780230542533927510061)
              ·
                refine ⟨81554167586453450222816273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217477780230542533927510061 81554167586453450222816273)
                ·
                  refine ⟨61165625689840087667112205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81554167586453450222816273 61165625689840087667112205)
                  ·
                    refine ⟨22937109633690032875167077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61165625689840087667112205 22937109633690032875167077)
                    ·
                      refine ⟨4300708056316881164093827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22937109633690032875167077 4300708056316881164093827)
                      ·
                        rfl

theorem cell23_8375599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_8375599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375599 prefixEnd_8375599 := by exact prefixLift 8375599
  have htrace : WordTrace (prefixWord ++ tailWord_8375599) baseStart_8375599 baseEnd_8375599 := by
    simpa [prefixWord, tailWord_8375599, baseEnd_8375599] using wordTrace_append hprefix tailTrace_8375599
  have hstable : (prefixWord ++ tailWord_8375599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375599).length < 2 ^ (prefixWord ++ tailWord_8375599).sum := by decide
  have hdescent : baseEnd_8375599 < baseStart_8375599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375633 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_8375633 : Nat := 118140960795 + 8375633 * 2 ^ 59
def prefixEnd_8375633 : Nat := 4983230072969 + 3 ^ 40 * 8375633 * 2
def baseEnd_8375633 : Nat := 4300725514659134031068671

theorem tailTrace_8375633 : CollatzResearch.WordTrace tailWord_8375633 prefixEnd_8375633 4300725514659134031068671 := by
  unfold tailWord_8375633
  simp only [CollatzResearch.WordTrace]
  refine ⟨305484432065519560078027553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203656288043679706718685035 305484432065519560078027553)
  ·
    refine ⟨229113324049139670058520665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305484432065519560078027553 229113324049139670058520665)
    ·
      refine ⟨171834993036854752543890499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229113324049139670058520665 171834993036854752543890499)
      ·
        refine ⟨257752489555282128815835749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171834993036854752543890499 257752489555282128815835749)
        ·
          refine ⟨48328591791615399152969203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257752489555282128815835749 48328591791615399152969203)
          ·
            refine ⟨72492887687423098729453805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48328591791615399152969203 72492887687423098729453805)
            ·
              refine ⟨27184832882783662023545177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72492887687423098729453805 27184832882783662023545177)
              ·
                refine ⟨20388624662087746517658883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27184832882783662023545177 20388624662087746517658883)
                ·
                  refine ⟨30582936993131619776488325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20388624662087746517658883 30582936993131619776488325)
                  ·
                    refine ⟨5734300686212178708091561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30582936993131619776488325 5734300686212178708091561)
                    ·
                      refine ⟨4300725514659134031068671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734300686212178708091561 4300725514659134031068671)
                      ·
                        rfl

theorem cell23_8375633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_8375633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375633 prefixEnd_8375633 := by exact prefixLift 8375633
  have htrace : WordTrace (prefixWord ++ tailWord_8375633) baseStart_8375633 baseEnd_8375633 := by
    simpa [prefixWord, tailWord_8375633, baseEnd_8375633] using wordTrace_append hprefix tailTrace_8375633
  have hstable : (prefixWord ++ tailWord_8375633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375633).length < 2 ^ (prefixWord ++ tailWord_8375633).sum := by decide
  have hdescent : baseEnd_8375633 < baseStart_8375633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375636 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_8375636 : Nat := 118140960795 + 8375636 * 2 ^ 59
def prefixEnd_8375636 : Nat := 4983230072969 + 3 ^ 40 * 8375636 * 2
def baseEnd_8375636 : Nat := 4300727055101097519331157

theorem tailTrace_8375636 : CollatzResearch.WordTrace tailWord_8375636 prefixEnd_8375636 4300727055101097519331157 := by
  unfold tailWord_8375636
  simp only [CollatzResearch.WordTrace]
  refine ⟨152742270742254345795193381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203656360989672461060257841 152742270742254345795193381)
  ·
    refine ⟨28639175764172689836598759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152742270742254345795193381 28639175764172689836598759)
    ·
      refine ⟨42958763646259034754898139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28639175764172689836598759 42958763646259034754898139)
      ·
        refine ⟨64438145469388552132347209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42958763646259034754898139 64438145469388552132347209)
        ·
          refine ⟨48328609102041414099260407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64438145469388552132347209 48328609102041414099260407)
          ·
            refine ⟨72492913653062121148890611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48328609102041414099260407 72492913653062121148890611)
            ·
              refine ⟨108739370479593181723335917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72492913653062121148890611 108739370479593181723335917)
              ·
                refine ⟨40777263929847443146250969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108739370479593181723335917 40777263929847443146250969)
                ·
                  refine ⟨30582947947385582359688227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40777263929847443146250969 30582947947385582359688227)
                  ·
                    refine ⟨45874421921078373539532341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30582947947385582359688227 45874421921078373539532341)
                    ·
                      refine ⟨4300727055101097519331157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45874421921078373539532341 4300727055101097519331157)
                      ·
                        rfl

theorem cell23_8375636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_8375636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375636 prefixEnd_8375636 := by exact prefixLift 8375636
  have htrace : WordTrace (prefixWord ++ tailWord_8375636) baseStart_8375636 baseEnd_8375636 := by
    simpa [prefixWord, tailWord_8375636, baseEnd_8375636] using wordTrace_append hprefix tailTrace_8375636
  have hstable : (prefixWord ++ tailWord_8375636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375636).length < 2 ^ (prefixWord ++ tailWord_8375636).sum := by decide
  have hdescent : baseEnd_8375636 < baseStart_8375636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375637 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_8375637 : Nat := 118140960795 + 8375637 * 2 ^ 59
def prefixEnd_8375637 : Nat := 4983230072969 + 3 ^ 40 * 8375637 * 2
def baseEnd_8375637 : Nat := 4300727568581752015418653

theorem tailTrace_8375637 : CollatzResearch.WordTrace tailWord_8375637 prefixEnd_8375637 4300727568581752015418653 := by
  unfold tailWord_8375637
  simp only [CollatzResearch.WordTrace]
  refine ⟨305484577957505068761173165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203656385305003379174115443 305484577957505068761173165)
  ·
    refine ⟨114556716734064400785439937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305484577957505068761173165 114556716734064400785439937)
    ·
      refine ⟨85917537550548300589079953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114556716734064400785439937 85917537550548300589079953)
      ·
        refine ⟨64438153162911225441809965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85917537550548300589079953 64438153162911225441809965)
        ·
          refine ⟨24164307436091709540678737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64438153162911225441809965 24164307436091709540678737)
          ·
            refine ⟨18123230577068782155509053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24164307436091709540678737 18123230577068782155509053)
            ·
              refine ⟨6796211466400793308315895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18123230577068782155509053 6796211466400793308315895)
              ·
                refine ⟨10194317199601189962473843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796211466400793308315895 10194317199601189962473843)
                ·
                  refine ⟨15291475799401784943710765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194317199601189962473843 15291475799401784943710765)
                  ·
                    refine ⟨5734303424775669353891537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15291475799401784943710765 5734303424775669353891537)
                    ·
                      refine ⟨4300727568581752015418653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734303424775669353891537 4300727568581752015418653)
                      ·
                        rfl

theorem cell23_8375637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_8375637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375637 prefixEnd_8375637 := by exact prefixLift 8375637
  have htrace : WordTrace (prefixWord ++ tailWord_8375637) baseStart_8375637 baseEnd_8375637 := by
    simpa [prefixWord, tailWord_8375637, baseEnd_8375637] using wordTrace_append hprefix tailTrace_8375637
  have hstable : (prefixWord ++ tailWord_8375637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375637).length < 2 ^ (prefixWord ++ tailWord_8375637).sum := by decide
  have hdescent : baseEnd_8375637 < baseStart_8375637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375645 : List Nat := [1, 4, 5, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8375645 : Nat := 118140960795 + 8375645 * 2 ^ 59
def prefixEnd_8375645 : Nat := 4983230072969 + 3 ^ 40 * 8375645 * 2
def baseEnd_8375645 : Nat := 4300731676426987984118617

theorem tailTrace_8375645 : CollatzResearch.WordTrace tailWord_8375645 prefixEnd_8375645 4300731676426987984118617 := by
  unfold tailWord_8375645
  simp only [CollatzResearch.WordTrace]
  refine ⟨305484869741476086127464389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203656579827650724084976259 305484869741476086127464389)
  ·
    refine ⟨57278413076526766148899573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305484869741476086127464389 57278413076526766148899573)
    ·
      refine ⟨5369851225924384326459335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57278413076526766148899573 5369851225924384326459335)
      ·
        refine ⟨8054776838886576489689003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369851225924384326459335 8054776838886576489689003)
        ·
          refine ⟨12082165258329864734533505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054776838886576489689003 12082165258329864734533505)
          ·
            refine ⟨9061623943747398550900129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12082165258329864734533505 9061623943747398550900129)
            ·
              refine ⟨6796217957810548913175097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9061623943747398550900129 6796217957810548913175097)
              ·
                refine ⟨5097163468357911684881323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6796217957810548913175097 5097163468357911684881323)
                ·
                  refine ⟨7645745202536867527321985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097163468357911684881323 7645745202536867527321985)
                  ·
                    refine ⟨5734308901902650645491489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645745202536867527321985 5734308901902650645491489)
                    ·
                      refine ⟨4300731676426987984118617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734308901902650645491489 4300731676426987984118617)
                      ·
                        rfl

theorem cell23_8375645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8375645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375645 prefixEnd_8375645 := by exact prefixLift 8375645
  have htrace : WordTrace (prefixWord ++ tailWord_8375645) baseStart_8375645 baseEnd_8375645 := by
    simpa [prefixWord, tailWord_8375645, baseEnd_8375645] using wordTrace_append hprefix tailTrace_8375645
  have hstable : (prefixWord ++ tailWord_8375645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375645).length < 2 ^ (prefixWord ++ tailWord_8375645).sum := by decide
  have hdescent : baseEnd_8375645 < baseStart_8375645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375649 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_8375649 : Nat := 118140960795 + 8375649 * 2 ^ 59
def prefixEnd_8375649 : Nat := 4983230072969 + 3 ^ 40 * 8375649 * 2
def baseEnd_8375649 : Nat := 4300733730349605968468597

theorem tailTrace_8375649 : CollatzResearch.WordTrace tailWord_8375649 prefixEnd_8375649 4300733730349605968468597 := by
  unfold tailWord_8375649
  simp only [CollatzResearch.WordTrace]
  refine ⟨305485015633461594810610001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203656677088974396540406667 305485015633461594810610001)
  ·
    refine ⟨229113761725096196107957501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305485015633461594810610001 229113761725096196107957501)
    ·
      refine ⟨85917660646911073540484063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229113761725096196107957501 85917660646911073540484063)
      ·
        refine ⟨128876490970366610310726095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85917660646911073540484063 128876490970366610310726095)
        ·
          refine ⟨193314736455549915466089143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128876490970366610310726095 193314736455549915466089143)
          ·
            refine ⟨289972104683324873199133715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193314736455549915466089143 289972104683324873199133715)
            ·
              refine ⟨434958157024987309798700573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289972104683324873199133715 434958157024987309798700573)
              ·
                refine ⟨163109308884370241174512715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434958157024987309798700573 163109308884370241174512715)
                ·
                  refine ⟨244663963326555361761769073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163109308884370241174512715 244663963326555361761769073)
                  ·
                    refine ⟨183497972494916521321326805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244663963326555361761769073 183497972494916521321326805)
                    ·
                      refine ⟨4300733730349605968468597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183497972494916521321326805 4300733730349605968468597)
                      ·
                        rfl

theorem cell23_8375649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_8375649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375649 prefixEnd_8375649 := by exact prefixLift 8375649
  have htrace : WordTrace (prefixWord ++ tailWord_8375649) baseStart_8375649 baseEnd_8375649 := by
    simpa [prefixWord, tailWord_8375649, baseEnd_8375649] using wordTrace_append hprefix tailTrace_8375649
  have hstable : (prefixWord ++ tailWord_8375649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375649).length < 2 ^ (prefixWord ++ tailWord_8375649).sum := by decide
  have hdescent : baseEnd_8375649 < baseStart_8375649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375699 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 10]
def baseStart_8375699 : Nat := 118140960795 + 8375699 * 2 ^ 59
def prefixEnd_8375699 : Nat := 4983230072969 + 3 ^ 40 * 8375699 * 2
def baseEnd_8375699 : Nat := 1433586468127443590947789

theorem tailTrace_8375699 : CollatzResearch.WordTrace tailWord_8375699 prefixEnd_8375699 1433586468127443590947789 := by
  unfold tailWord_8375699
  simp only [CollatzResearch.WordTrace]
  refine ⟨305486839283280453349930151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203657892855520302233286767 305486839283280453349930151)
  ·
    refine ⟨458230258924920680024895227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305486839283280453349930151 458230258924920680024895227)
    ·
      refine ⟨687345388387381020037342841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458230258924920680024895227 687345388387381020037342841)
      ·
        refine ⟨515509041290535765028007131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687345388387381020037342841 515509041290535765028007131)
        ·
          refine ⟨773263561935803647542010697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515509041290535765028007131 773263561935803647542010697)
          ·
            refine ⟨579947671451852735656508023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773263561935803647542010697 579947671451852735656508023)
            ·
              refine ⟨869921507177779103484762035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579947671451852735656508023 869921507177779103484762035)
              ·
                refine ⟨1304882260766668655227143053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869921507177779103484762035 1304882260766668655227143053)
                ·
                  refine ⟨489330847787500745710178645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1304882260766668655227143053 489330847787500745710178645)
                  ·
                    refine ⟨1433586468127443590947789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 489330847787500745710178645 1433586468127443590947789)
                    ·
                      rfl

theorem cell23_8375699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_8375699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375699 prefixEnd_8375699 := by exact prefixLift 8375699
  have htrace : WordTrace (prefixWord ++ tailWord_8375699) baseStart_8375699 baseEnd_8375699 := by
    simpa [prefixWord, tailWord_8375699, baseEnd_8375699] using wordTrace_append hprefix tailTrace_8375699
  have hstable : (prefixWord ++ tailWord_8375699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375699).length < 2 ^ (prefixWord ++ tailWord_8375699).sum := by decide
  have hdescent : baseEnd_8375699 < baseStart_8375699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375790 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_8375790 : Nat := 118140960795 + 8375790 * 2 ^ 59
def prefixEnd_8375790 : Nat := 4983230072969 + 3 ^ 40 * 8375790 * 2
def baseEnd_8375790 : Nat := 4300806131121889916805449

theorem tailTrace_8375790 : CollatzResearch.WordTrace tailWord_8375790 prefixEnd_8375790 4300806131121889916805449 := by
  unfold tailWord_8375790
  simp only [CollatzResearch.WordTrace]
  refine ⟨38186269790743846986436603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203660105550633850594328549 38186269790743846986436603)
  ·
    refine ⟨57279404686115770479654905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38186269790743846986436603 57279404686115770479654905)
    ·
      refine ⟨42959553514586827859741179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57279404686115770479654905 42959553514586827859741179)
      ·
        refine ⟨64439330271880241789611769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42959553514586827859741179 64439330271880241789611769)
        ·
          refine ⟨48329497703910181342208827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64439330271880241789611769 48329497703910181342208827)
          ·
            refine ⟨72494246555865272013313241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48329497703910181342208827 72494246555865272013313241)
            ·
              refine ⟨54370684916898954009984931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72494246555865272013313241 54370684916898954009984931)
              ·
                refine ⟨81556027375348431014977397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54370684916898954009984931 81556027375348431014977397)
                ·
                  refine ⟨7645877566438915407654131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81556027375348431014977397 7645877566438915407654131)
                  ·
                    refine ⟨11468816349658373111481197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7645877566438915407654131 11468816349658373111481197)
                    ·
                      refine ⟨4300806131121889916805449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468816349658373111481197 4300806131121889916805449)
                      ·
                        rfl

theorem cell23_8375790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_8375790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375790 prefixEnd_8375790 := by exact prefixLift 8375790
  have htrace : WordTrace (prefixWord ++ tailWord_8375790) baseStart_8375790 baseEnd_8375790 := by
    simpa [prefixWord, tailWord_8375790, baseEnd_8375790] using wordTrace_append hprefix tailTrace_8375790
  have hstable : (prefixWord ++ tailWord_8375790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375790).length < 2 ^ (prefixWord ++ tailWord_8375790).sum := by decide
  have hdescent : baseEnd_8375790 < baseStart_8375790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375793 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_8375793 : Nat := 118140960795 + 8375793 * 2 ^ 59
def prefixEnd_8375793 : Nat := 4983230072969 + 3 ^ 40 * 8375793 * 2
def baseEnd_8375793 : Nat := 1433602557187951135022645

theorem tailTrace_8375793 : CollatzResearch.WordTrace tailWord_8375793 prefixEnd_8375793 1433602557187951135022645 := by
  unfold tailWord_8375793
  simp only [CollatzResearch.WordTrace]
  refine ⟨305490267744939907403852033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203660178496626604935901355 305490267744939907403852033)
  ·
    refine ⟨229117700808704930552889025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305490267744939907403852033 229117700808704930552889025)
    ·
      refine ⟨171838275606528697914666769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229117700808704930552889025 171838275606528697914666769)
      ·
        refine ⟨128878706704896523436000077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171838275606528697914666769 128878706704896523436000077)
        ·
          refine ⟨48329515014336196288500029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128878706704896523436000077 48329515014336196288500029)
          ·
            refine ⟨18123568130376073608187511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48329515014336196288500029 18123568130376073608187511)
            ·
              refine ⟨27185352195564110412281267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18123568130376073608187511 27185352195564110412281267)
              ·
                refine ⟨40778028293346165618421901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27185352195564110412281267 40778028293346165618421901)
                ·
                  refine ⟨15291760610004812106908213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40778028293346165618421901 15291760610004812106908213)
                  ·
                    refine ⟨1433602557187951135022645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15291760610004812106908213 1433602557187951135022645)
                    ·
                      rfl

theorem cell23_8375793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_8375793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375793 prefixEnd_8375793 := by exact prefixLift 8375793
  have htrace : WordTrace (prefixWord ++ tailWord_8375793) baseStart_8375793 baseEnd_8375793 := by
    simpa [prefixWord, tailWord_8375793, baseEnd_8375793] using wordTrace_append hprefix tailTrace_8375793
  have hstable : (prefixWord ++ tailWord_8375793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375793).length < 2 ^ (prefixWord ++ tailWord_8375793).sum := by decide
  have hdescent : baseEnd_8375793 < baseStart_8375793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375800 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_8375800 : Nat := 118140960795 + 8375800 * 2 ^ 59
def prefixEnd_8375800 : Nat := 4983230072969 + 3 ^ 40 * 8375800 * 2
def baseEnd_8375800 : Nat := 4300811265928434877680403

theorem tailTrace_8375800 : CollatzResearch.WordTrace tailWord_8375800 prefixEnd_8375800 4300811265928434877680403 := by
  unfold tailWord_8375800
  simp only [CollatzResearch.WordTrace]
  refine ⟨152745261527957273799678427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203660348703943031732904569 152745261527957273799678427)
  ·
    refine ⟨229117892291935910699517641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152745261527957273799678427 229117892291935910699517641)
    ·
      refine ⟨171838419218951933024638231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229117892291935910699517641 171838419218951933024638231)
      ·
        refine ⟨257757628828427899536957347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171838419218951933024638231 257757628828427899536957347)
        ·
          refine ⟨386636443242641849305436021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257757628828427899536957347 386636443242641849305436021)
          ·
            refine ⟨36247166553997673372384627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386636443242641849305436021 36247166553997673372384627)
            ·
              refine ⟨54370749830996510058576941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36247166553997673372384627 54370749830996510058576941)
              ·
                refine ⟨20389031186623691271966353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54370749830996510058576941 20389031186623691271966353)
                ·
                  refine ⟨15291773389967768453974765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20389031186623691271966353 15291773389967768453974765)
                  ·
                    refine ⟨5734415021237913170240537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15291773389967768453974765 5734415021237913170240537)
                    ·
                      refine ⟨4300811265928434877680403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734415021237913170240537 4300811265928434877680403)
                      ·
                        rfl

theorem cell23_8375800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_8375800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375800 prefixEnd_8375800 := by exact prefixLift 8375800
  have htrace : WordTrace (prefixWord ++ tailWord_8375800) baseStart_8375800 baseEnd_8375800 := by
    simpa [prefixWord, tailWord_8375800, baseEnd_8375800] using wordTrace_append hprefix tailTrace_8375800
  have hstable : (prefixWord ++ tailWord_8375800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375800).length < 2 ^ (prefixWord ++ tailWord_8375800).sum := by decide
  have hdescent : baseEnd_8375800 < baseStart_8375800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375840 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_8375840 : Nat := 118140960795 + 8375840 * 2 ^ 59
def prefixEnd_8375840 : Nat := 4983230072969 + 3 ^ 40 * 8375840 * 2
def baseEnd_8375840 : Nat := 1433610601718204907060073

theorem tailTrace_8375840 : CollatzResearch.WordTrace tailWord_8375840 prefixEnd_8375840 1433610601718204907060073 := by
  unfold tailWord_8375840
  simp only [CollatzResearch.WordTrace]
  refine ⟨152745990987884817215406487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203661321317179756287208649 152745990987884817215406487)
  ·
    refine ⟨229118986481827225823109731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152745990987884817215406487 229118986481827225823109731)
    ·
      refine ⟨343678479722740838734664597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229118986481827225823109731 343678479722740838734664597)
      ·
        refine ⟨16109928737003476815687403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 343678479722740838734664597 16109928737003476815687403)
        ·
          refine ⟨24164893105505215223531105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109928737003476815687403 24164893105505215223531105)
          ·
            refine ⟨18123669829128911417648329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24164893105505215223531105 18123669829128911417648329)
            ·
              refine ⟨13592752371846683563236247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18123669829128911417648329 13592752371846683563236247)
              ·
                refine ⟨20389128557770025344854371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13592752371846683563236247 20389128557770025344854371)
                ·
                  refine ⟨30583692836655038017281557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20389128557770025344854371 30583692836655038017281557)
                  ·
                    refine ⟨1433610601718204907060073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30583692836655038017281557 1433610601718204907060073)
                    ·
                      rfl

theorem cell23_8375840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_8375840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375840 prefixEnd_8375840 := by exact prefixLift 8375840
  have htrace : WordTrace (prefixWord ++ tailWord_8375840) baseStart_8375840 baseEnd_8375840 := by
    simpa [prefixWord, tailWord_8375840, baseEnd_8375840] using wordTrace_append hprefix tailTrace_8375840
  have hstable : (prefixWord ++ tailWord_8375840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375840).length < 2 ^ (prefixWord ++ tailWord_8375840).sum := by decide
  have hdescent : baseEnd_8375840 < baseStart_8375840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375850 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_8375850 : Nat := 118140960795 + 8375850 * 2 ^ 59
def prefixEnd_8375850 : Nat := 4983230072969 + 3 ^ 40 * 8375850 * 2
def baseEnd_8375850 : Nat := 4300836939961159682055173

theorem tailTrace_8375850 : CollatzResearch.WordTrace tailWord_8375850 prefixEnd_8375850 4300836939961159682055173 := by
  unfold tailWord_8375850
  simp only [CollatzResearch.WordTrace]
  refine ⟨76373086676433351534669251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203661564470488937425784669 76373086676433351534669251)
  ·
    refine ⟨114559630014650027302003877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76373086676433351534669251 114559630014650027302003877)
    ·
      refine ⟨21479930627746880119125727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114559630014650027302003877 21479930627746880119125727)
      ·
        refine ⟨32219895941620320178688591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21479930627746880119125727 32219895941620320178688591)
        ·
          refine ⟨48329843912430480268032887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32219895941620320178688591 48329843912430480268032887)
          ·
            refine ⟨72494765868645720402049331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48329843912430480268032887 72494765868645720402049331)
            ·
              refine ⟨108742148802968580603073997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72494765868645720402049331 108742148802968580603073997)
              ·
                refine ⟨40778305801113217726152749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108742148802968580603073997 40778305801113217726152749)
                ·
                  refine ⟨15291864675417456647307281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40778305801113217726152749 15291864675417456647307281)
                  ·
                    refine ⟨11468898506563092485480461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15291864675417456647307281 11468898506563092485480461)
                    ·
                      refine ⟨4300836939961159682055173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468898506563092485480461 4300836939961159682055173)
                      ·
                        rfl

theorem cell23_8375850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_8375850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375850 prefixEnd_8375850 := by exact prefixLift 8375850
  have htrace : WordTrace (prefixWord ++ tailWord_8375850) baseStart_8375850 baseEnd_8375850 := by
    simpa [prefixWord, tailWord_8375850, baseEnd_8375850] using wordTrace_append hprefix tailTrace_8375850
  have hstable : (prefixWord ++ tailWord_8375850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375850).length < 2 ^ (prefixWord ++ tailWord_8375850).sum := by decide
  have hdescent : baseEnd_8375850 < baseStart_8375850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375864 : List Nat := [2, 1, 2, 1, 4, 2, 1, 5, 1, 2, 2]
def baseStart_8375864 : Nat := 118140960795 + 8375864 * 2 ^ 59
def prefixEnd_8375864 : Nat := 4983230072969 + 3 ^ 40 * 8375864 * 2
def baseEnd_8375864 : Nat := 4300844128690322627280109

theorem tailTrace_8375864 : CollatzResearch.WordTrace tailWord_8375864 prefixEnd_8375864 4300844128690322627280109 := by
  unfold tailWord_8375864
  simp only [CollatzResearch.WordTrace]
  refine ⟨152746428663841343264843323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203661904885121791019791097 152746428663841343264843323)
  ·
    refine ⟨229119642995762014897264985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152746428663841343264843323 229119642995762014897264985)
    ·
      refine ⟨171839732246821511172948739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229119642995762014897264985 171839732246821511172948739)
      ·
        refine ⟨257759598370232266759423109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171839732246821511172948739 257759598370232266759423109)
        ·
          refine ⟨48329924694418550017391833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257759598370232266759423109 48329924694418550017391833)
          ·
            refine ⟨36247443520813912513043875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48329924694418550017391833 36247443520813912513043875)
            ·
              refine ⟨54371165281220868769565813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36247443520813912513043875 54371165281220868769565813)
              ·
                refine ⟨5097296745114456447146795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54371165281220868769565813 5097296745114456447146795)
                ·
                  refine ⟨7645945117671684670720193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097296745114456447146795 7645945117671684670720193)
                  ·
                    refine ⟨5734458838253763503040145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7645945117671684670720193 5734458838253763503040145)
                    ·
                      refine ⟨4300844128690322627280109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734458838253763503040145 4300844128690322627280109)
                      ·
                        rfl

theorem cell23_8375864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_8375864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375864 prefixEnd_8375864 := by exact prefixLift 8375864
  have htrace : WordTrace (prefixWord ++ tailWord_8375864) baseStart_8375864 baseEnd_8375864 := by
    simpa [prefixWord, tailWord_8375864, baseEnd_8375864] using wordTrace_append hprefix tailTrace_8375864
  have hstable : (prefixWord ++ tailWord_8375864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375864).length < 2 ^ (prefixWord ++ tailWord_8375864).sum := by decide
  have hdescent : baseEnd_8375864 < baseStart_8375864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375894 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_8375894 : Nat := 118140960795 + 8375894 * 2 ^ 59
def prefixEnd_8375894 : Nat := 4983230072969 + 3 ^ 40 * 8375894 * 2
def baseEnd_8375894 : Nat := 4300859533109957509904971

theorem tailTrace_8375894 : CollatzResearch.WordTrace tailWord_8375894 prefixEnd_8375894 4300859533109957509904971 := by
  unfold tailWord_8375894
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093371969848375103329921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203662634345049334435519157 19093371969848375103329921)
  ·
    refine ⟨14320028977386281327497441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19093371969848375103329921 14320028977386281327497441)
    ·
      refine ⟨10740021733039710995623081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14320028977386281327497441 10740021733039710995623081)
      ·
        refine ⟨8055016299779783246717311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10740021733039710995623081 8055016299779783246717311)
        ·
          refine ⟨12082524449669674870075967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055016299779783246717311 12082524449669674870075967)
          ·
            refine ⟨18123786674504512305113951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082524449669674870075967 18123786674504512305113951)
            ·
              refine ⟨27185680011756768457670927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18123786674504512305113951 27185680011756768457670927)
              ·
                refine ⟨40778520017635152686506391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27185680011756768457670927 40778520017635152686506391)
                ·
                  refine ⟨61167780026452729029759587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40778520017635152686506391 61167780026452729029759587)
                  ·
                    refine ⟨91751670039679093544639381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61167780026452729029759587 91751670039679093544639381)
                    ·
                      refine ⟨4300859533109957509904971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91751670039679093544639381 4300859533109957509904971)
                      ·
                        rfl

theorem cell23_8375894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_8375894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375894 prefixEnd_8375894 := by exact prefixLift 8375894
  have htrace : WordTrace (prefixWord ++ tailWord_8375894) baseStart_8375894 baseEnd_8375894 := by
    simpa [prefixWord, tailWord_8375894, baseEnd_8375894] using wordTrace_append hprefix tailTrace_8375894
  have hstable : (prefixWord ++ tailWord_8375894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375894).length < 2 ^ (prefixWord ++ tailWord_8375894).sum := by decide
  have hdescent : baseEnd_8375894 < baseStart_8375894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375901 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8375901 : Nat := 118140960795 + 8375901 * 2 ^ 59
def prefixEnd_8375901 : Nat := 4983230072969 + 3 ^ 40 * 8375901 * 2
def baseEnd_8375901 : Nat := 4300863127474538982517439

theorem tailTrace_8375901 : CollatzResearch.WordTrace tailWord_8375901 prefixEnd_8375901 4300863127474538982517439 := by
  unfold tailWord_8375901
  simp only [CollatzResearch.WordTrace]
  refine ⟨305494206828548641848783557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203662804552365761232522371 305494206828548641848783557)
  ·
    refine ⟨57280163780352870346646917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305494206828548641848783557 57280163780352870346646917)
    ·
      refine ⟨10740030708816163189996297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57280163780352870346646917 10740030708816163189996297)
      ·
        refine ⟨8055023031612122392497223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10740030708816163189996297 8055023031612122392497223)
        ·
          refine ⟨12082534547418183588745835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055023031612122392497223 12082534547418183588745835)
          ·
            refine ⟨18123801821127275383118753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082534547418183588745835 18123801821127275383118753)
            ·
              refine ⟨13592851365845456537339065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18123801821127275383118753 13592851365845456537339065)
              ·
                refine ⟨10194638524384092403004299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13592851365845456537339065 10194638524384092403004299)
                ·
                  refine ⟨15291957786576138604506449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194638524384092403004299 15291957786576138604506449)
                  ·
                    refine ⟨11468968339932103953379837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15291957786576138604506449 11468968339932103953379837)
                    ·
                      refine ⟨4300863127474538982517439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11468968339932103953379837 4300863127474538982517439)
                      ·
                        rfl

theorem cell23_8375901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8375901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375901 prefixEnd_8375901 := by exact prefixLift 8375901
  have htrace : WordTrace (prefixWord ++ tailWord_8375901) baseStart_8375901 baseEnd_8375901 := by
    simpa [prefixWord, tailWord_8375901, baseEnd_8375901] using wordTrace_append hprefix tailTrace_8375901
  have hstable : (prefixWord ++ tailWord_8375901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375901).length < 2 ^ (prefixWord ++ tailWord_8375901).sum := by decide
  have hdescent : baseEnd_8375901 < baseStart_8375901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375907 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 1, 3, 2]
def baseStart_8375907 : Nat := 118140960795 + 8375907 * 2 ^ 59
def prefixEnd_8375907 : Nat := 4983230072969 + 3 ^ 40 * 8375907 * 2
def baseEnd_8375907 : Nat := 4300866208358465959042411

theorem tailTrace_8375907 : CollatzResearch.WordTrace tailWord_8375907 prefixEnd_8375907 4300866208358465959042411 := by
  unfold tailWord_8375907
  simp only [CollatzResearch.WordTrace]
  refine ⟨305494425666526904873501975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203662950444351269915667983 305494425666526904873501975)
  ·
    refine ⟨458241638499790357310252963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305494425666526904873501975 458241638499790357310252963)
    ·
      refine ⟨687362457749685535965379445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458241638499790357310252963 687362457749685535965379445)
      ·
        refine ⟨64440230414033018996754323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 687362457749685535965379445 64440230414033018996754323)
        ·
          refine ⟨96660345621049528495131485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64440230414033018996754323 96660345621049528495131485)
          ·
            refine ⟨36247629607893573185674307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96660345621049528495131485 36247629607893573185674307)
            ·
              refine ⟨54371444411840359778511461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36247629607893573185674307 54371444411840359778511461)
              ·
                refine ⟨10194645827220067458470899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54371444411840359778511461 10194645827220067458470899)
                ·
                  refine ⟨15291968740830101187706349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194645827220067458470899 15291968740830101187706349)
                  ·
                    refine ⟨5734488277811287945389881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15291968740830101187706349 5734488277811287945389881)
                    ·
                      refine ⟨4300866208358465959042411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734488277811287945389881 4300866208358465959042411)
                      ·
                        rfl

theorem cell23_8375907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_8375907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375907 prefixEnd_8375907 := by exact prefixLift 8375907
  have htrace : WordTrace (prefixWord ++ tailWord_8375907) baseStart_8375907 baseEnd_8375907 := by
    simpa [prefixWord, tailWord_8375907, baseEnd_8375907] using wordTrace_append hprefix tailTrace_8375907
  have hstable : (prefixWord ++ tailWord_8375907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375907).length < 2 ^ (prefixWord ++ tailWord_8375907).sum := by decide
  have hdescent : baseEnd_8375907 < baseStart_8375907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375973 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_8375973 : Nat := 118140960795 + 8375973 * 2 ^ 59
def prefixEnd_8375973 : Nat := 4983230072969 + 3 ^ 40 * 8375973 * 2
def baseEnd_8375973 : Nat := 1433633366027220900272369

theorem tailTrace_8375973 : CollatzResearch.WordTrace tailWord_8375973 prefixEnd_8375973 1433633366027220900272369 := by
  unfold tailWord_8375973
  simp only [CollatzResearch.WordTrace]
  refine ⟨305496832884287798145404573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203664555256191865430269715 305496832884287798145404573)
  ·
    refine ⟨114561312331607924304526715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305496832884287798145404573 114561312331607924304526715)
    ·
      refine ⟨171841968497411886456790073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114561312331607924304526715 171841968497411886456790073)
      ·
        refine ⟨128881476373058914842592555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171841968497411886456790073 128881476373058914842592555)
        ·
          refine ⟨193322214559588372263888833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128881476373058914842592555 193322214559588372263888833)
          ·
            refine ⟨144991660919691279197916625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193322214559588372263888833 144991660919691279197916625)
            ·
              refine ⟨108743745689768459398437469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144991660919691279197916625 108743745689768459398437469)
              ·
                refine ⟨40778904633663172274414051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108743745689768459398437469 40778904633663172274414051)
                ·
                  refine ⟨61168356950494758411621077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40778904633663172274414051 61168356950494758411621077)
                  ·
                    refine ⟨1433633366027220900272369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61168356950494758411621077 1433633366027220900272369)
                    ·
                      rfl

theorem cell23_8375973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_8375973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375973 prefixEnd_8375973 := by exact prefixLift 8375973
  have htrace : WordTrace (prefixWord ++ tailWord_8375973) baseStart_8375973 baseEnd_8375973 := by
    simpa [prefixWord, tailWord_8375973, baseEnd_8375973] using wordTrace_append hprefix tailTrace_8375973
  have hstable : (prefixWord ++ tailWord_8375973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375973).length < 2 ^ (prefixWord ++ tailWord_8375973).sum := by decide
  have hdescent : baseEnd_8375973 < baseStart_8375973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375980 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_8375980 : Nat := 118140960795 + 8375980 * 2 ^ 59
def prefixEnd_8375980 : Nat := 4983230072969 + 3 ^ 40 * 8375980 * 2
def baseEnd_8375980 : Nat := 4300903692446244173429575

theorem tailTrace_8375980 : CollatzResearch.WordTrace tailWord_8375980 prefixEnd_8375980 4300903692446244173429575 := by
  unfold tailWord_8375980
  simp only [CollatzResearch.WordTrace]
  refine ⟨152748544097631219170454697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203664725463508292227272929 152748544097631219170454697)
  ·
    refine ⟨114561408073223414377841023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152748544097631219170454697 114561408073223414377841023)
    ·
      refine ⟨171842112109835121566761535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114561408073223414377841023 171842112109835121566761535)
      ·
        refine ⟨257763168164752682350142303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171842112109835121566761535 257763168164752682350142303)
        ·
          refine ⟨386644752247129023525213455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257763168164752682350142303 386644752247129023525213455)
          ·
            refine ⟨579967128370693535287820183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386644752247129023525213455 579967128370693535287820183)
            ·
              refine ⟨869950692556040302931730275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579967128370693535287820183 869950692556040302931730275)
              ·
                refine ⟨1304926038834060454397595413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869950692556040302931730275 1304926038834060454397595413)
                ·
                  refine ⟨61168408070346583799887285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1304926038834060454397595413 61168408070346583799887285)
                  ·
                    refine ⟨5734538256594992231239433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61168408070346583799887285 5734538256594992231239433)
                    ·
                      refine ⟨4300903692446244173429575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734538256594992231239433 4300903692446244173429575)
                      ·
                        rfl

theorem cell23_8375980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_8375980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375980 prefixEnd_8375980 := by exact prefixLift 8375980
  have htrace : WordTrace (prefixWord ++ tailWord_8375980) baseStart_8375980 baseEnd_8375980 := by
    simpa [prefixWord, tailWord_8375980, baseEnd_8375980] using wordTrace_append hprefix tailTrace_8375980
  have hstable : (prefixWord ++ tailWord_8375980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375980).length < 2 ^ (prefixWord ++ tailWord_8375980).sum := by decide
  have hdescent : baseEnd_8375980 < baseStart_8375980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375983 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_8375983 : Nat := 118140960795 + 8375983 * 2 ^ 59
def prefixEnd_8375983 : Nat := 4983230072969 + 3 ^ 40 * 8375983 * 2
def baseEnd_8375983 : Nat := 4300905232888207661692061

theorem tailTrace_8375983 : CollatzResearch.WordTrace tailWord_8375983 prefixEnd_8375983 4300905232888207661692061 := by
  unfold tailWord_8375983
  simp only [CollatzResearch.WordTrace]
  refine ⟨305497197614251569853268603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203664798409501046568845735 305497197614251569853268603)
  ·
    refine ⟨458245796421377354779902905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305497197614251569853268603 458245796421377354779902905)
    ·
      refine ⟨343684347316033016084927179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458245796421377354779902905 343684347316033016084927179)
      ·
        refine ⟨515526520974049524127390769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343684347316033016084927179 515526520974049524127390769)
        ·
          refine ⟨386644890730537143095543077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515526520974049524127390769 386644890730537143095543077)
          ·
            refine ⟨72495917011975714330414327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386644890730537143095543077 72495917011975714330414327)
            ·
              refine ⟨108743875517963571495621491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72495917011975714330414327 108743875517963571495621491)
              ·
                refine ⟨163115813276945357243432237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108743875517963571495621491 163115813276945357243432237)
                ·
                  refine ⟨61168429978854508966287089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163115813276945357243432237 61168429978854508966287089)
                  ·
                    refine ⟨45876322484140881724715317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61168429978854508966287089 45876322484140881724715317)
                    ·
                      refine ⟨4300905232888207661692061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45876322484140881724715317 4300905232888207661692061)
                      ·
                        rfl

theorem cell23_8375983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_8375983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375983 prefixEnd_8375983 := by exact prefixLift 8375983
  have htrace : WordTrace (prefixWord ++ tailWord_8375983) baseStart_8375983 baseEnd_8375983 := by
    simpa [prefixWord, tailWord_8375983, baseEnd_8375983] using wordTrace_append hprefix tailTrace_8375983
  have hstable : (prefixWord ++ tailWord_8375983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375983).length < 2 ^ (prefixWord ++ tailWord_8375983).sum := by decide
  have hdescent : baseEnd_8375983 < baseStart_8375983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375994 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_8375994 : Nat := 118140960795 + 8375994 * 2 ^ 59
def prefixEnd_8375994 : Nat := 4983230072969 + 3 ^ 40 * 8375994 * 2
def baseEnd_8375994 : Nat := 477878986797267457628279

theorem tailTrace_8375994 : CollatzResearch.WordTrace tailWord_8375994 prefixEnd_8375994 477878986797267457628279 := by
  unfold tailWord_8375994
  simp only [CollatzResearch.WordTrace]
  refine ⟨76374399704302929682979759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203665065878141145821279357 76374399704302929682979759)
  ·
    refine ⟨114561599556454394524469639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76374399704302929682979759 114561599556454394524469639)
    ·
      refine ⟨171842399334681591786704459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114561599556454394524469639 171842399334681591786704459)
      ·
        refine ⟨257763599002022387680056689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171842399334681591786704459 257763599002022387680056689)
        ·
          refine ⟨193322699251516790760042517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257763599002022387680056689 193322699251516790760042517)
          ·
            refine ⟨9062001527414849566876993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193322699251516790760042517 9062001527414849566876993)
            ·
              refine ⟨6796501145561137175157745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9062001527414849566876993 6796501145561137175157745)
              ·
                refine ⟨5097375859170852881368309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6796501145561137175157745 5097375859170852881368309)
                ·
                  refine ⟨477878986797267457628279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5097375859170852881368309 477878986797267457628279)
                  ·
                    rfl

theorem cell23_8375994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_8375994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8375994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8375994 prefixEnd_8375994 := by exact prefixLift 8375994
  have htrace : WordTrace (prefixWord ++ tailWord_8375994) baseStart_8375994 baseEnd_8375994 := by
    simpa [prefixWord, tailWord_8375994, baseEnd_8375994] using wordTrace_append hprefix tailTrace_8375994
  have hstable : (prefixWord ++ tailWord_8375994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375994).length < 2 ^ (prefixWord ++ tailWord_8375994).sum := by decide
  have hdescent : baseEnd_8375994 < baseStart_8375994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376040 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_8376040 : Nat := 118140960795 + 8376040 * 2 ^ 59
def prefixEnd_8376040 : Nat := 4983230072969 + 3 ^ 40 * 8376040 * 2
def baseEnd_8376040 : Nat := 4300934501285513938679299

theorem tailTrace_8376040 : CollatzResearch.WordTrace tailWord_8376040 prefixEnd_8376040 4300934501285513938679299 := by
  unfold tailWord_8376040
  simp only [CollatzResearch.WordTrace]
  refine ⟨152749638287522534294046787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203666184383363379058729049 152749638287522534294046787)
  ·
    refine ⟨229124457431283801441070181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152749638287522534294046787 229124457431283801441070181)
    ·
      refine ⟨42960835768365712770200659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229124457431283801441070181 42960835768365712770200659)
      ·
        refine ⟨64441253652548569155300989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960835768365712770200659 64441253652548569155300989)
        ·
          refine ⟨24165470119705713433237871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64441253652548569155300989 24165470119705713433237871)
          ·
            refine ⟨36248205179558570149856807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24165470119705713433237871 36248205179558570149856807)
            ·
              refine ⟨54372307769337855224785211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36248205179558570149856807 54372307769337855224785211)
              ·
                refine ⟨81558461654006782837177817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54372307769337855224785211 81558461654006782837177817)
                ·
                  refine ⟨61168846240505087127883363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81558461654006782837177817 61168846240505087127883363)
                  ·
                    refine ⟨91753269360757630691825045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61168846240505087127883363 91753269360757630691825045)
                    ·
                      refine ⟨4300934501285513938679299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91753269360757630691825045 4300934501285513938679299)
                      ·
                        rfl

theorem cell23_8376040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_8376040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376040 prefixEnd_8376040 := by exact prefixLift 8376040
  have htrace : WordTrace (prefixWord ++ tailWord_8376040) baseStart_8376040 baseEnd_8376040 := by
    simpa [prefixWord, tailWord_8376040, baseEnd_8376040] using wordTrace_append hprefix tailTrace_8376040
  have hstable : (prefixWord ++ tailWord_8376040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376040).length < 2 ^ (prefixWord ++ tailWord_8376040).sum := by decide
  have hdescent : baseEnd_8376040 < baseStart_8376040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376050 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_8376050 : Nat := 118140960795 + 8376050 * 2 ^ 59
def prefixEnd_8376050 : Nat := 4983230072969 + 3 ^ 40 * 8376050 * 2
def baseEnd_8376050 : Nat := 477882181788006544394917

theorem tailTrace_8376050 : CollatzResearch.WordTrace tailWord_8376050 prefixEnd_8376050 477882181788006544394917 := by
  unfold tailWord_8376050
  simp only [CollatzResearch.WordTrace]
  refine ⟨76374910326252210073989401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203666427536672560197305069 76374910326252210073989401)
  ·
    refine ⟨57281182744689157555492051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76374910326252210073989401 57281182744689157555492051)
    ·
      refine ⟨85921774117033736333238077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57281182744689157555492051 85921774117033736333238077)
      ·
        refine ⟨32220665293887651124964279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85921774117033736333238077 32220665293887651124964279)
        ·
          refine ⟨48330997940831476687446419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32220665293887651124964279 48330997940831476687446419)
          ·
            refine ⟨72496496911247215031169629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48330997940831476687446419 72496496911247215031169629)
            ·
              refine ⟨27186186341717705636688611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72496496911247215031169629 27186186341717705636688611)
              ·
                refine ⟨40779279512576558455032917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27186186341717705636688611 40779279512576558455032917)
                ·
                  refine ⟨477882181788006544394917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40779279512576558455032917 477882181788006544394917)
                  ·
                    rfl

theorem cell23_8376050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_8376050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376050 prefixEnd_8376050 := by exact prefixLift 8376050
  have htrace : WordTrace (prefixWord ++ tailWord_8376050) baseStart_8376050 baseEnd_8376050 := by
    simpa [prefixWord, tailWord_8376050, baseEnd_8376050] using wordTrace_append hprefix tailTrace_8376050
  have hstable : (prefixWord ++ tailWord_8376050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376050).length < 2 ^ (prefixWord ++ tailWord_8376050).sum := by decide
  have hdescent : baseEnd_8376050 < baseStart_8376050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376054 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_8376054 : Nat := 118140960795 + 8376054 * 2 ^ 59
def prefixEnd_8376054 : Nat := 4983230072969 + 3 ^ 40 * 8376054 * 2
def baseEnd_8376054 : Nat := 1433647230004892294634745

theorem tailTrace_8376054 : CollatzResearch.WordTrace tailWord_8376054 prefixEnd_8376054 1433647230004892294634745 := by
  unfold tailWord_8376054
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093736699812146811193951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203666524797996232652735477 19093736699812146811193951)
  ·
    refine ⟨28640605049718220216790927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093736699812146811193951 28640605049718220216790927)
    ·
      refine ⟨42960907574577330325186391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28640605049718220216790927 42960907574577330325186391)
      ·
        refine ⟨64441361361865995487779587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42960907574577330325186391 64441361361865995487779587)
        ·
          refine ⟨96662042042798993231669381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64441361361865995487779587 96662042042798993231669381)
          ·
            refine ⟨18124132883024811230938009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96662042042798993231669381 18124132883024811230938009)
            ·
              refine ⟨13593099662268608423203507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18124132883024811230938009 13593099662268608423203507)
              ·
                refine ⟨20389649493402912634805261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13593099662268608423203507 20389649493402912634805261)
                ·
                  refine ⟨7646118560026092238051973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20389649493402912634805261 7646118560026092238051973)
                  ·
                    refine ⟨1433647230004892294634745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7646118560026092238051973 1433647230004892294634745)
                    ·
                      rfl

theorem cell23_8376054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_8376054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376054 prefixEnd_8376054 := by exact prefixLift 8376054
  have htrace : WordTrace (prefixWord ++ tailWord_8376054) baseStart_8376054 baseEnd_8376054 := by
    simpa [prefixWord, tailWord_8376054, baseEnd_8376054] using wordTrace_append hprefix tailTrace_8376054
  have hstable : (prefixWord ++ tailWord_8376054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376054).length < 2 ^ (prefixWord ++ tailWord_8376054).sum := by decide
  have hdescent : baseEnd_8376054 < baseStart_8376054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376097 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_8376097 : Nat := 118140960795 + 8376097 * 2 ^ 59
def prefixEnd_8376097 : Nat := 4983230072969 + 3 ^ 40 * 8376097 * 2
def baseEnd_8376097 : Nat := 1433654589894273405222179

theorem tailTrace_8376097 : CollatzResearch.WordTrace tailWord_8376097 prefixEnd_8376097 1433654589894273405222179 := by
  unfold tailWord_8376097
  simp only [CollatzResearch.WordTrace]
  refine ⟨305501355535838567322918545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203667570357225711548612363 305501355535838567322918545)
  ·
    refine ⟨229126016651878925492188909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305501355535838567322918545 229126016651878925492188909)
    ·
      refine ⟨85922256244454597059570841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229126016651878925492188909 85922256244454597059570841)
      ·
        refine ⟨64441692183340947794678131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85922256244454597059570841 64441692183340947794678131)
        ·
          refine ⟨96662538275011421692017197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64441692183340947794678131 96662538275011421692017197)
          ·
            refine ⟨36248451853129283134506449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96662538275011421692017197 36248451853129283134506449)
            ·
              refine ⟨27186338889846962350879837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36248451853129283134506449 27186338889846962350879837)
              ·
                refine ⟨10194877083692610881579939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27186338889846962350879837 10194877083692610881579939)
                ·
                  refine ⟨15292315625538916322369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194877083692610881579939 15292315625538916322369909)
                  ·
                    refine ⟨1433654589894273405222179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15292315625538916322369909 1433654589894273405222179)
                    ·
                      rfl

theorem cell23_8376097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_8376097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376097 prefixEnd_8376097 := by exact prefixLift 8376097
  have htrace : WordTrace (prefixWord ++ tailWord_8376097) baseStart_8376097 baseEnd_8376097 := by
    simpa [prefixWord, tailWord_8376097, baseEnd_8376097] using wordTrace_append hprefix tailTrace_8376097
  have hstable : (prefixWord ++ tailWord_8376097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376097).length < 2 ^ (prefixWord ++ tailWord_8376097).sum := by decide
  have hdescent : baseEnd_8376097 < baseStart_8376097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376104 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_8376104 : Nat := 118140960795 + 8376104 * 2 ^ 59
def prefixEnd_8376104 : Nat := 4983230072969 + 3 ^ 40 * 8376104 * 2
def baseEnd_8376104 : Nat := 4300967364047401688279005

theorem tailTrace_8376104 : CollatzResearch.WordTrace tailWord_8376104 prefixEnd_8376104 4300967364047401688279005 := by
  unfold tailWord_8376104
  simp only [CollatzResearch.WordTrace]
  refine ⟨152750805423406603759211683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203667740564542138345615577 152750805423406603759211683)
  ·
    refine ⟨229126208135109905638817525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152750805423406603759211683 229126208135109905638817525)
    ·
      refine ⟨21480582012666553653639143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229126208135109905638817525 21480582012666553653639143)
      ·
        refine ⟨32220873018999830480458715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21480582012666553653639143 32220873018999830480458715)
        ·
          refine ⟨48331309528499745720688073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32220873018999830480458715 48331309528499745720688073)
          ·
            refine ⟨36248482146374809290516055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48331309528499745720688073 36248482146374809290516055)
            ·
              refine ⟨54372723219562213935774083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36248482146374809290516055 54372723219562213935774083)
              ·
                refine ⟨81559084829343320903661125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54372723219562213935774083 81559084829343320903661125)
                ·
                  refine ⟨15292328405501872669436461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81559084829343320903661125 15292328405501872669436461)
                  ·
                    refine ⟨5734623152063202251038673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15292328405501872669436461 5734623152063202251038673)
                    ·
                      refine ⟨4300967364047401688279005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734623152063202251038673 4300967364047401688279005)
                      ·
                        rfl

theorem cell23_8376104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_8376104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376104 prefixEnd_8376104 := by exact prefixLift 8376104
  have htrace : WordTrace (prefixWord ++ tailWord_8376104) baseStart_8376104 baseEnd_8376104 := by
    simpa [prefixWord, tailWord_8376104, baseEnd_8376104] using wordTrace_append hprefix tailTrace_8376104
  have hstable : (prefixWord ++ tailWord_8376104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376104).length < 2 ^ (prefixWord ++ tailWord_8376104).sum := by decide
  have hdescent : baseEnd_8376104 < baseStart_8376104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376137 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_8376137 : Nat := 118140960795 + 8376137 * 2 ^ 59
def prefixEnd_8376137 : Nat := 4983230072969 + 3 ^ 40 * 8376137 * 2
def baseEnd_8376137 : Nat := 4300984308909000059166353

theorem tailTrace_8376137 : CollatzResearch.WordTrace tailWord_8376137 prefixEnd_8376137 4300984308909000059166353 := by
  unfold tailWord_8376137
  simp only [CollatzResearch.WordTrace]
  refine ⟨305502814455693654154374665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203668542970462436102916443 305502814455693654154374665)
  ·
    refine ⟨229127110841770240615780999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305502814455693654154374665 229127110841770240615780999)
    ·
      refine ⟨343690666262655360923671499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229127110841770240615780999 343690666262655360923671499)
      ·
        refine ⟨515535999393983041385507249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343690666262655360923671499 515535999393983041385507249)
        ·
          refine ⟨386651999545487281039130437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515535999393983041385507249 386651999545487281039130437)
          ·
            refine ⟨72497249914778865194836957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386651999545487281039130437 72497249914778865194836957)
            ·
              refine ⟨27186468718042074448063859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72497249914778865194836957 27186468718042074448063859)
              ·
                refine ⟨40779703077063111672095789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27186468718042074448063859 40779703077063111672095789)
                ·
                  refine ⟨15292388653898666877035921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40779703077063111672095789 15292388653898666877035921)
                  ·
                    refine ⟨11469291490424000157776941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15292388653898666877035921 11469291490424000157776941)
                    ·
                      refine ⟨4300984308909000059166353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469291490424000157776941 4300984308909000059166353)
                      ·
                        rfl

theorem cell23_8376137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_8376137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376137 prefixEnd_8376137 := by exact prefixLift 8376137
  have htrace : WordTrace (prefixWord ++ tailWord_8376137) baseStart_8376137 baseEnd_8376137 := by
    simpa [prefixWord, tailWord_8376137, baseEnd_8376137] using wordTrace_append hprefix tailTrace_8376137
  have hstable : (prefixWord ++ tailWord_8376137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376137).length < 2 ^ (prefixWord ++ tailWord_8376137).sum := by decide
  have hdescent : baseEnd_8376137 < baseStart_8376137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376151 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 1, 1, 4]
def baseStart_8376151 : Nat := 118140960795 + 8376151 * 2 ^ 59
def prefixEnd_8376151 : Nat := 4983230072969 + 3 ^ 40 * 8376151 * 2
def baseEnd_8376151 : Nat := 4300991497638163004391289

theorem tailTrace_8376151 : CollatzResearch.WordTrace tailWord_8376151 prefixEnd_8376151 4300991497638163004391289 := by
  unfold tailWord_8376151
  simp only [CollatzResearch.WordTrace]
  refine ⟨305503325077642934545384307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203668883385095289696922871 305503325077642934545384307)
  ·
    refine ⟨458254987616464401818076461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305503325077642934545384307 458254987616464401818076461)
    ·
      refine ⟨171845620356174150681778673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458254987616464401818076461 171845620356174150681778673)
      ·
        refine ⟨128884215267130613011334005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171845620356174150681778673 128884215267130613011334005)
        ·
          refine ⟨12082895181293494969812563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128884215267130613011334005 12082895181293494969812563)
          ·
            refine ⟨18124342771940242454718845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082895181293494969812563 18124342771940242454718845)
            ·
              refine ⟨6796628539477590920519567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18124342771940242454718845 6796628539477590920519567)
              ·
                refine ⟨10194942809216386380779351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796628539477590920519567 10194942809216386380779351)
                ·
                  refine ⟨15292414213824579571169027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194942809216386380779351 15292414213824579571169027)
                  ·
                    refine ⟨22938621320736869356753541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15292414213824579571169027 22938621320736869356753541)
                    ·
                      refine ⟨4300991497638163004391289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22938621320736869356753541 4300991497638163004391289)
                      ·
                        rfl

theorem cell23_8376151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_8376151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376151 prefixEnd_8376151 := by exact prefixLift 8376151
  have htrace : WordTrace (prefixWord ++ tailWord_8376151) baseStart_8376151 baseEnd_8376151 := by
    simpa [prefixWord, tailWord_8376151, baseEnd_8376151] using wordTrace_append hprefix tailTrace_8376151
  have hstable : (prefixWord ++ tailWord_8376151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376151).length < 2 ^ (prefixWord ++ tailWord_8376151).sum := by decide
  have hdescent : baseEnd_8376151 < baseStart_8376151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376167 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_8376167 : Nat := 118140960795 + 8376167 * 2 ^ 59
def prefixEnd_8376167 : Nat := 4983230072969 + 3 ^ 40 * 8376167 * 2
def baseEnd_8376167 : Nat := 4300999713328634941791215

theorem tailTrace_8376167 : CollatzResearch.WordTrace tailWord_8376167 prefixEnd_8376167 4300999713328634941791215 := by
  unfold tailWord_8376167
  simp only [CollatzResearch.WordTrace]
  refine ⟨305503908645584969277966755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203669272430389979518644503 305503908645584969277966755)
  ·
    refine ⟨458255862968377453916950133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305503908645584969277966755 458255862968377453916950133)
    ·
      refine ⟨42961487153285386304714075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458255862968377453916950133 42961487153285386304714075)
      ·
        refine ⟨64442230729928079457071113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42961487153285386304714075 64442230729928079457071113)
        ·
          refine ⟨48331673047446059592803335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64442230729928079457071113 48331673047446059592803335)
          ·
            refine ⟨72497509571169089389205003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48331673047446059592803335 72497509571169089389205003)
            ·
              refine ⟨108746264356753634083807505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72497509571169089389205003 108746264356753634083807505)
              ·
                refine ⟨81559698267565225562855629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108746264356753634083807505 81559698267565225562855629)
                ·
                  refine ⟨30584886850336959586070861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81559698267565225562855629 30584886850336959586070861)
                  ·
                    refine ⟨11469332568876359844776573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30584886850336959586070861 11469332568876359844776573)
                    ·
                      refine ⟨4300999713328634941791215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11469332568876359844776573 4300999713328634941791215)
                      ·
                        rfl

theorem cell23_8376167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_8376167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376167 prefixEnd_8376167 := by exact prefixLift 8376167
  have htrace : WordTrace (prefixWord ++ tailWord_8376167) baseStart_8376167 baseEnd_8376167 := by
    simpa [prefixWord, tailWord_8376167, baseEnd_8376167] using wordTrace_append hprefix tailTrace_8376167
  have hstable : (prefixWord ++ tailWord_8376167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376167).length < 2 ^ (prefixWord ++ tailWord_8376167).sum := by decide
  have hdescent : baseEnd_8376167 < baseStart_8376167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376168 : List Nat := [2, 1, 4, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_8376168 : Nat := 118140960795 + 8376168 * 2 ^ 59
def prefixEnd_8376168 : Nat := 4983230072969 + 3 ^ 40 * 8376168 * 2
def baseEnd_8376168 : Nat := 4301000226809289437878711

theorem tailTrace_8376168 : CollatzResearch.WordTrace tailWord_8376168 prefixEnd_8376168 4301000226809289437878711 := by
  unfold tailWord_8376168
  simp only [CollatzResearch.WordTrace]
  refine ⟨152751972559290673224376579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203669296745720897632502105 152751972559290673224376579)
  ·
    refine ⟨229127958838936009836564869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152751972559290673224376579 229127958838936009836564869)
    ·
      refine ⟨42961492282300501844355913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229127958838936009836564869 42961492282300501844355913)
      ·
        refine ⟨32221119211725376383266935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42961492282300501844355913 32221119211725376383266935)
        ·
          refine ⟨48331678817588064574900403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32221119211725376383266935 48331678817588064574900403)
          ·
            refine ⟨72497518226382096862350605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48331678817588064574900403 72497518226382096862350605)
            ·
              refine ⟨27186569334893286323381477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72497518226382096862350605 27186569334893286323381477)
              ·
                refine ⟨5097481750292491185634027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27186569334893286323381477 5097481750292491185634027)
                ·
                  refine ⟨7646222625438736778451041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097481750292491185634027 7646222625438736778451041)
                  ·
                    refine ⟨5734666969079052583838281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7646222625438736778451041 5734666969079052583838281)
                    ·
                      refine ⟨4301000226809289437878711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5734666969079052583838281 4301000226809289437878711)
                      ·
                        rfl

theorem cell23_8376168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_8376168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376168 prefixEnd_8376168 := by exact prefixLift 8376168
  have htrace : WordTrace (prefixWord ++ tailWord_8376168) baseStart_8376168 baseEnd_8376168 := by
    simpa [prefixWord, tailWord_8376168, baseEnd_8376168] using wordTrace_append hprefix tailTrace_8376168
  have hstable : (prefixWord ++ tailWord_8376168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376168).length < 2 ^ (prefixWord ++ tailWord_8376168).sum := by decide
  have hdescent : baseEnd_8376168 < baseStart_8376168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8376174 : List Nat := [4, 1, 2, 3, 1, 3, 1, 8]
def baseStart_8376174 : Nat := 118140960795 + 8376174 * 2 ^ 59
def prefixEnd_8376174 : Nat := 4983230072969 + 3 ^ 40 * 8376174 * 2
def baseEnd_8376174 : Nat := 159296418803452459792729

theorem tailTrace_8376174 : CollatzResearch.WordTrace tailWord_8376174 prefixEnd_8376174 159296418803452459792729 := by
  unfold tailWord_8376174
  simp only [CollatzResearch.WordTrace]
  refine ⟨38188020494569951184183947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203669442637706406315647717 38188020494569951184183947)
  ·
    refine ⟨57282030741854926776275921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38188020494569951184183947 57282030741854926776275921)
    ·
      refine ⟨42961523056391195082206941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57282030741854926776275921 42961523056391195082206941)
      ·
        refine ⟨16110571146146698155827603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42961523056391195082206941 16110571146146698155827603)
        ·
          refine ⟨24165856719220047233741405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16110571146146698155827603 24165856719220047233741405)
          ·
            refine ⟨9062196269707517712653027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24165856719220047233741405 9062196269707517712653027)
            ·
              refine ⟨13593294404561276568979541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062196269707517712653027 13593294404561276568979541)
              ·
                refine ⟨159296418803452459792729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13593294404561276568979541 159296418803452459792729)
                ·
                  rfl

theorem cell23_8376174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_8376174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8376174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8376174 prefixEnd_8376174 := by exact prefixLift 8376174
  have htrace : WordTrace (prefixWord ++ tailWord_8376174) baseStart_8376174 baseEnd_8376174 := by
    simpa [prefixWord, tailWord_8376174, baseEnd_8376174] using wordTrace_append hprefix tailTrace_8376174
  have hstable : (prefixWord ++ tailWord_8376174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8376174).length < 2 ^ (prefixWord ++ tailWord_8376174).sum := by decide
  have hdescent : baseEnd_8376174 < baseStart_8376174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8376174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
